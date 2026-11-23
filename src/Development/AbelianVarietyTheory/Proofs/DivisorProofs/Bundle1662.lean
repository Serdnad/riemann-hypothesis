module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumEquationsInArchimedeanDarbouxCoordinat
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Std.Tactic.BVDecide.Normalize.Bool
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem

@[expose] public section

section

noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD GlobalTheory.VacBridge

namespace GlobalTheory.HoweD

theorem exists_bridgeD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (ε : InfinitePlace F → ℤˣ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ (u u' u₁ : Matrix α β (AE F E)) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧ (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
        (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        (∀ w, u₁.map (piInf (τ w)) = A w * (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a b A C ε hcm hfr
  have := hcm.1
  obtain ⟨-, hA, hC⟩ := hfr
  choose IA hIA using fun w =>
    frame_inv _ (A w) (Jm (P w) (Q w)) (jm_mul_self (P w) (Q w)) (hA w).1 (hA w).2
  choose IC hIC using fun w =>
    frame_inv _ (C w) (Jm (R w) (S w)) (jm_mul_self (R w) (S w)) (hC w).1 (hC w).2
  have hback : ∀ w (X : Matrix α β ℂ), A w * (IA w * X * (IC w)ᵀ) * (C w)ᵀ = X := by
    intro w X
    have hCt : (IC w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, (hIC w).2, Matrix.transpose_one]
    calc _ = (A w * IA w) * X * ((IC w)ᵀ * (C w)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [(hIA w).2, hCt, Matrix.one_mul, Matrix.mul_one]
  have hfwd : ∀ w (c : Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), IA w * (A w * c * (C w)ᵀ) * (IC w)ᵀ = c := by
    intro w c
    have hCt : (C w)ᵀ * (IC w)ᵀ = 1 := by rw [← Matrix.transpose_mul, (hIC w).1, Matrix.transpose_one]
    calc _ = (IA w * A w) * c * ((C w)ᵀ * (IC w)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = c := by rw [(hIA w).1, hCt, Matrix.one_mul, Matrix.mul_one]
  let Ψl : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun y w => IA w * (mkD d y).map (piInf (τ w)) * (IC w)ᵀ
      map_add' := fun y y' => by
        funext w
        simp only [mkD_add, Pi.add_apply]
        rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r y => by
        funext w
        simp only [mkD_smul_real, map_smul_piInf, ext_realAd, RingHom.id_apply, Pi.smul_apply]
        rw [Matrix.mul_smul, Matrix.smul_mul]
        ext i j
        simp [Complex.real_smul] }
  have hΨl : ∀ y w, A w * Ψl y w * (C w)ᵀ = (mkD d y).map (piInf (τ w)) := fun y w => hback w _
  have hinj : Function.Injective Ψl := by
    intro y y' h
    have hu : mkD d y = mkD d y' := eq_of_at_map σ hcm τ (at_mkD d y) (at_mkD d y') fun w => by
      rw [← hΨl, ← hΨl, h]
    rw [← coord_mkD d y, ← coord_mkD d y', hu]
  have hsurj : Function.Surjective Ψl := by
    intro c
    obtain ⟨u, hu, hM⟩ := exists_at_map σ hcm τ (fun w => A w * c w * (C w)ᵀ)
    refine ⟨coord d u, funext fun w => ?_⟩
    show IA w * (mkD d (coord d u)).map (piInf (τ w)) * (IC w)ᵀ = c w
    rw [mkD_coord d hu, hM w, hfwd]
  let Ψ := LinearEquiv.ofBijective Ψl ⟨hinj, hsurj⟩
  let L : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun c w => Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))
      map_add' := fun c c' => by
        funext w
        simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add]
      map_smul' := fun r c => by
        funext w
        simp only [Pi.smul_apply, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
        exact smul_comm _ _ _ }
  let Pm : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun c w => (if ε w = -1 then (1 : ℂ) else 0) • c w
      map_add' := fun c c' => by
        funext w
        simp only [Pi.add_apply, smul_add]
      map_smul' := fun r c => by
        funext w
        simp only [Pi.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hLL : ∀ c, L (L c) = -c := by
    intro c
    funext w
    show Complex.I • (Jm (P w) (Q w) * (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * Jm (R w) (S w)) = -c w
    have key : Jm (P w) (Q w) * (Jm (P w) (Q w) * c w * Jm (R w) (S w)) * Jm (R w) (S w) = c w := by
      calc _ = (Jm (P w) (Q w) * Jm (P w) (Q w)) * c w * (Jm (R w) (S w) * Jm (R w) (S w)) := by
            simp only [Matrix.mul_assoc]
        _ = c w := by rw [jm_mul_self, jm_mul_self, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, key, Complex.I_mul_I, neg_one_smul]
  have hLP : ∀ c, L (Pm c) = Pm (L c) := by
    intro c
    funext w
    show Complex.I • (Jm (P w) (Q w) * ((if ε w = -1 then (1 : ℂ) else 0) • c w) * Jm (R w) (S w)) =
      (if ε w = -1 then (1 : ℂ) else 0) • (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w)))
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  let tm : AF F := ((fun w => if ε w = -1 then 1 else 0 : InfiniteAdeleRing F), 0)
  have htm : tm * tm = tm := by
    refine Prod.ext (funext fun w => ?_) ?_
    · show (if ε w = -1 then (1 : w.Completion) else 0) * (if ε w = -1 then 1 else 0) = if ε w = -1 then 1 else 0
      split_ifs <;> simp
    · show (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * 0 = 0
      exact mul_zero _
  have htt : evI F tm * evI F tm = evI F tm := by rw [← evI_mul, htm]
  have hext : ∀ w, InfinitePlace.Completion.extensionEmbedding w (tm.1 w) = if ε w = -1 then 1 else 0 := by
    intro w
    show InfinitePlace.Completion.extensionEmbedding w (if ε w = -1 then (1 : w.Completion) else 0) = _
    split_ifs <;> simp
  have hΨe : ∀ y, Ψl (mulP (evI F tm) y) = Pm (Ψl y) := by
    intro y
    funext w
    show IA w * (mkD d (mulP (evI F tm) y)).map (piInf (τ w)) * (IC w)ᵀ =
      (if ε w = -1 then (1 : ℂ) else 0) • (IA w * (mkD d y).map (piInf (τ w)) * (IC w)ᵀ)
    rw [mkD_mulP, map_smul_piInf, hext, Matrix.mul_smul, Matrix.smul_mul]
  let J : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :=
    (Ψ.symm : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] _).comp (L.comp Ψl)
  have hΨJ : ∀ y, Ψl (J y) = L (Ψl y) := fun y => Ψ.apply_symm_apply _
  refine ⟨J, mulP (evI F tm), mulC (evI F tm), ?_, ?_, ?_, fun y => rfl, ?_, ?_⟩
  · intro y
    apply hinj
    rw [hΨJ, hΨJ, hLL, map_neg]
  · intro y
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show evI F tm * (evI F tm * y.1 i) = evI F tm * y.1 i
      rw [← mul_assoc, htt]
    · show evI F tm * (evI F tm * y.2 i) = evI F tm * y.2 i
      rw [← mul_assoc, htt]
  · intro y
    apply hinj
    rw [hΨJ, hΨe, hΨe, hΨJ, hLP]
  · intro y x
    simp only [trPair_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show x i * (evI F tm * y.2 i) = (evI F tm * x i) * y.2 i
    ring
  · intro y
    refine ⟨mkD d y, mkD d (J (y - (2 : ℝ) • mulP (evI F tm) y)), mkD d (J y), Ψl y, at_mkD d _, at_mkD d _,
      at_mkD d _, fun w => (hΨl y w).symm, fun w => ?_, fun w => ?_, coord_mkD d _, coord_mkD d _, coord_mkD d _⟩
    · rw [← hΨl, hΨJ, map_sub, map_smul, hΨe]
      show A w * (Complex.I • (Jm (P w) (Q w) * (Ψl y w - (2 : ℝ) • ((if ε w = -1 then (1 : ℂ) else 0) • Ψl y w)) *
          Jm (R w) (S w))) * (C w)ᵀ =
        A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * Ψl y w * Jm (R w) (S w))) * (C w)ᵀ
      congr 2
      generalize Ψl y w = X
      rcases Int.units_eq_one_or (ε w) with h1 | h1
      · rw [h1, if_neg (by decide)]
        simp
      · rw [h1, if_pos rfl, one_smul, two_smul, sub_add_cancel_left]
        simp [Matrix.mul_neg, Matrix.neg_mul]
    · rw [← hΨl, hΨJ]
      rfl

end GlobalTheory.HoweD

end
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem diag_re_le_of_near_min {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (G : ι → ι → Module.End ℂ M) (α β : ℂ) (R : ℝ)
    (hR : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F →
      (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ,
      (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) →
      ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) →
      (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R)
    (hG : IsGl G) (hq : ∀ a b, qop G α β a b = 0) (hL : LocU s G) (U : Submodule ℂ M) (hU : UnitOn s G U) (ω : ℝ)
    (hω : ∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s G v = (ω' : ℂ) • v → ω < ω' + 1)
    (hUe : ∀ u ∈ U, cas s G u = (ω : ℂ) • u) :
    ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, G a a u = m • u → m.re ≤ R :=
  GlobalTheory.T.blockUnitary_diagonal_le_of_eigenvalue_bound ι M s G U R hU (fun x y hy hyU hf hs => hR M G hG hq hL ω hω x y hy hf hs (fun a => hUe _ (hyU a)))

theorem exists_unitOn_diag_bounded : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β α' β' : ℂ), ∃ R : ℝ,
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), Nontrivial M → IsGl F →
    (∀ a b, qop F α β a b = 0) → (∀ a b, qop (negT F) α' β' a b = 0) → LocU s F →
    ∃ U : Submodule ℂ M, U ≠ ⊥ ∧ UnitOn s F U ∧ ∀ a, ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → |m.re| ≤ R := by
  intro ι _ _ s α β α' β'
  obtain ⟨R1, h1⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι s α β
  obtain ⟨R2, h2⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι (fun a => !s a) α β
  obtain ⟨R3, h3⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι s α' β'
  obtain ⟨R4, h4⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι (fun a => !s a) α' β'
  refine ⟨max (max R1 R2) (max R3 R4), ?_⟩
  intro M _ _ F hnt hG hq hq' hL
  obtain ⟨hGn, hcn, hcs, hUs, hLs⟩ := sym_negT_swap ι M s F
  obtain ⟨-, hcn', hcs', hUs', hLs'⟩ := sym_negT_swap ι M s (negT F)
  let S : Set ℝ := {ω' | ∃ v : M, v ≠ 0 ∧ cas s F v = (ω' : ℂ) • v}
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    obtain ⟨U, hxU, hU⟩ := hL {x}
    have hne : U ≠ ⊥ := by
      intro h
      have := hxU x (Finset.mem_singleton_self x)
      rw [h, Submodule.mem_bot] at this
      exact hx this
    obtain ⟨ω, v, -, hv, hcv⟩ := (GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hU).2 hne
    exact ⟨ω, v, hv, hcv⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, fun ω' hω' => ?_⟩
    obtain ⟨v, hv, hcv⟩ := hω'
    obtain ⟨U, hvU, hU⟩ := hL {v}
    have := (GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hU).1 (ω' : ℂ) v (hvU v (Finset.mem_singleton_self v)) hv hcv
    simpa using this.2
  obtain ⟨ω, ⟨v, hv, hcv⟩, hωlt⟩ := exists_lt_of_csInf_lt hSne (lt_add_one (sInf S))
  have hω : ∀ (ω' : ℝ) (w : M), w ≠ 0 → cas s F w = (ω' : ℂ) • w → ω < ω' + 1 := fun ω' w hw hcw => by
    have := csInf_le hSbdd ⟨w, hw, hcw⟩
    linarith
  obtain ⟨U0, hvU0, hU0⟩ := hL {v}
  let U : Submodule ℂ M := U0 ⊓ LinearMap.ker (cas s F - (ω : ℂ) • (1 : Module.End ℂ M))
  have hUe : ∀ u ∈ U, cas s F u = (ω : ℂ) • u := fun u hu => by
    have h2 := hu.2
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
    simpa using h2
  have hvU : v ∈ U := ⟨hvU0 v (Finset.mem_singleton_self v), by
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]; simpa using hcv⟩
  have hUst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U := by
    intro a b hab u hu
    refine ⟨hU0.2.1 a b hab u hu.1, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    have hc := congrArg (fun T : Module.End ℂ M => T u) (GlobalTheory.T.blockDiagonalFibreCasimir_commute_sameBlock_unit ι M s F hG a b hab)
    simp only [Module.End.mul_apply] at hc
    rw [hc, hUe u hu]
    simp
  have hU : UnitOn s F U := GlobalTheory.T.isBlockUnitaryFiniteSubspace_of_le_stable ι M s F U0 U hU0 inf_le_left hUst
  refine ⟨U, fun h => hv (by rw [h, Submodule.mem_bot] at hvU; exact hvU), hU, ?_⟩
  intro a u hu hu0 m hm
  have b1 := diag_re_le_of_near_min s F α β R1 h1 hG hq hL U hU ω hω hUe
  have b2 := diag_re_le_of_near_min (fun a => !s a) F α β R2 h2 hG hq (hLs hL).2 U (hUs U hU).2 ω
    (by rw [hcs]; exact hω) (by rw [hcs]; exact hUe)
  have b3 := diag_re_le_of_near_min s (negT F) α' β' R3 h3 (hGn hG) hq' (hLs hL).1 U (hUs U hU).1 ω
    (by rw [hcn]; exact hω) (by rw [hcn]; exact hUe)
  have b4 := diag_re_le_of_near_min (fun a => !s a) (negT F) α' β' R4 h4 (hGn hG) hq' (hLs' (hLs hL).1).2 U
    (hUs' U (hUs U hU).1).2 ω (by rw [hcs', hcn]; exact hω) (by rw [hcs', hcn]; exact hUe)
  have hmn : negT F a a u = (-m) • u := by simp [negT, hm]
  have l1 : R1 ≤ max (max R1 R2) (max R3 R4) := (le_max_left _ _).trans (le_max_left _ _)
  have l2 : R2 ≤ max (max R1 R2) (max R3 R4) := (le_max_right _ _).trans (le_max_left _ _)
  have l3 : R3 ≤ max (max R1 R2) (max R3 R4) := (le_max_left _ _).trans (le_max_right _ _)
  have l4 : R4 ≤ max (max R1 R2) (max R3 R4) := (le_max_right _ _).trans (le_max_right _ _)
  rw [abs_le]
  cases hsa : s a
  · have e1 := b2 a (by simp [hsa]) u hu hu0 m hm
    have e2 := b4 a (by simp [hsa]) u hu hu0 (-m) hmn
    rw [Complex.neg_re] at e2
    constructor <;> linarith
  · have e1 := b1 a hsa u hu hu0 m hm
    have e2 := b3 a hsa u hu hu0 (-m) hmn
    rw [Complex.neg_re] at e2
    constructor <;> linarith

end GlobalTheory.HoweR
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem recVal_iso_symm : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ T, IsMix q e T →
    ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r),
    (∀ L L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → recVal (T e L) L M hr = recVal (T e L') L' M hr) ∧
    (∀ (L : Fin e → HermLB q) (τ : Equiv.Perm (Fin e)),
      recVal (T e fun a => L (τ a)) (fun a => L (τ a)) M hr = recVal (T e L) L M hr) ∧
    (∀ (L : Fin e → HermLB q) (M' : HermLB q), M.Isometric M' → ∃ (r' : M'.B.ι → Y.functionFieldˣ)
      (hr' : IsRatSec M'.B r'), recVal (T e L) L M' hr' = recVal (T e L) L M hr) := by
  intro _ k _ Y _ _ q hq e hY T hT M r hr
  have hd : ∀ z : Y, ((M.div hr).mult z : ℝ) ≠ 0 → HasDim z e := fun z hz =>
    ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq e hY).1 z).1
      (CartierDiv.coheight_eq_one_of_mult_ne_zero fun h => hz (by rw [h]; simp))
  refine ⟨fun L L' h => ?_, fun L τ => ?_, fun L M' h => ?_⟩
  · unfold recVal
    rw [(GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr k Y q e L M r hr).1 L' h]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((M.div hr).mult z : ℝ) = 0
    · simp [hz]
    · rw [hT.iso e L L' z le_rfl (hd z hz) h]
  · unfold recVal
    rw [(GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr k Y q e L M r hr).2.1 τ]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((M.div hr).mult z : ℝ) = 0
    · simp [hz]
    · rw [hT.symm e L τ z le_rfl (hd z hz)]
  · obtain ⟨r', hr', hdiv, hlog⟩ := h.exists_isRatSec hr
    refine ⟨r', hr', ?_⟩
    unfold recVal
    rw [(GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr k Y q e L M r hr).2.2 M' r' hr' hdiv hlog, hdiv]

end GlobalTheory.MixHt
end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HatInt in

theorem _root_.GlobalTheory.T.levelPoint_smul_integral_of_fourierCoeff_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → ∀ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q ≠ 0 → ∀ s : 𝓞 D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → s ∈ PP.asIdeal) → ∀ b, ∃ z : Dw.La, s • (cSep l₂ • levRep (q b)) = l₂.M • z := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i H Dw ι t l₂ φ hφ q hq s hs b
  obtain ⟨e, -, he⟩ := hφ
  have hM : l₂.M ≠ 0 := by
    have := l₂.three_le
    omega
  have hdvd : ∀ w : Dw.La, (l₂.M : ℤ) ∣ Dw.EF w (s • (cSep l₂ • levRep (q b))) := by
    intro w
    let single : Fin (Vc D i).rank → Dw.La := Pi.single b w
    let shift : Fin (Vc D i).rank → Dw.La := fun j => H.bar s • single j
    have hinv : ∀ x, φ (x + fun j => Submodule.Quotient.mk (shift j)) = φ x := by
      intro x
      obtain ⟨y, rfl⟩ : ∃ y : Fin (Vc D i).rank → Dw.La,
          x = fun j => Submodule.Quotient.mk (y j) :=
        ⟨fun j => qRep (x j), funext fun j =>
          (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x j))).symm⟩
      have hshift := (he (fun j => y j + shift j)).2
      have horig := (he y).2
      simp only [RingHom.id_apply] at hshift horig
      have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t →
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun j => ι (y j + shift j)) =
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun j => ι (y j)) := by
        intro PP hP
        have hmap : (fun j => ι (y j + shift j)) =
            fun j => ι (y j) + ((H.bar s : 𝓞 D.host.E) : D.host.E) • ι (single j) := by
          funext j
          change ι (y j + H.bar s • single j) = _
          rw [map_add (f := _), map_smul]
          rfl
        rw [hmap, uMat_add_smul, sig_bar]
        exact redM_add_smul PP _ _ (he y).1 (he _).1 s (hs PP hP)
      rw [omegaK_congr _ _ _ (fun PP hP => hred PP (Or.inl hP)),
        omegaQ_congr _ _ _ _ _ _ (fun PP hP => hred PP (Or.inr hP)), ← horig] at hshift
      change φ (fun j => Submodule.Quotient.mk (y j) + Submodule.Quotient.mk (shift j)) = _
      simpa only [Submodule.Quotient.mk_add] using hshift
    have hpair := dvd_of_invariant l₂ φ q hq shift hinv
    unfold Formalism.L2.Pj.pairL at hpair
    rw [Finset.sum_eq_single b] at hpair
    · simpa [shift, single, Dw.adj, LevelPairing.bar_bar] using hpair
    · intro j _ hj
      simp [shift, single, Pi.single_eq_of_ne hj]
    · simp
  obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (s • (cSep l₂ • levRep (q b))) l₂.M hM (fun y => by
    have halt := Dw.alt (y + s • (cSep l₂ • levRep (q b)))
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt, zero_add, add_zero] at halt
    have hskew : Dw.EF (s • (cSep l₂ • levRep (q b))) y = -Dw.EF y (s • (cSep l₂ • levRep (q b))) := by
      linarith
    rw [hskew]
    exact (hdvd y).neg_right)
  exact ⟨z, by rw [hz, natCast_zsmul]⟩
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.separable_formGroup_element_fixes_unique_positive_line : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z := by
  first | (exact @GlobalTheory.LKCx.fixL_pos_unique_of_sep) | (exact GlobalTheory.LKCx.fixL_pos_unique_of_sep) | (intros; apply GlobalTheory.LKCx.fixL_pos_unique_of_sep  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem ptMap_isHolo : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str),
    (atlas X σ).IsHolo (atlas Y σ) (ptMap σ f hf) := fun _ _ _ _ _ f _ =>
  ⟨CxPts.continuous_of_comp (f := f) fun _ => rfl, fun j i => AlgChart.holo_map (f := f) (fun _ => rfl) j i⟩

end GlobalTheory.ChernCalc
end
