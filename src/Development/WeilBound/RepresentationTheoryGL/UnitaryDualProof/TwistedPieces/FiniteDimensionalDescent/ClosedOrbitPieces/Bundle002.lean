module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.Bundle001
public import Mathlib.Algebra.Field.IsField
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Instances.Matrix
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TrOrbA
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}

def Th (e : Matrix (Fin N) (Fin N) k) : Module.End k (Wd e) →ₗ[k] Matrix (Fin N) (Fin N) k where
  toFun f := LinearMap.toMatrix' ((Wd e).subtype ∘ₗ f ∘ₗ Pe e)
  map_add' f g := by rw [← map_add (f := _)]; congr 1
  map_smul' c f := by rw [RingHom.id_apply, ← map_smul]; congr 1

lemma Th_mulVec (f : Module.End k (Wd e)) (v : Fin N → k) : Th e f *ᵥ v = (f (Pe e v) : Fin N → k) := by
  show LinearMap.toMatrix' ((Wd e).subtype ∘ₗ f ∘ₗ Pe e) *ᵥ v = _
  exact toMatrix'_mulVec' _ v

lemma Th_inj : Function.Injective (Th (k := k) (N := N) e) := by
  intro f g h
  ext w : 1
  obtain ⟨v, rfl⟩ := Pe_surj e w
  have := congrArg (· *ᵥ v) h
  simp only [Th_mulVec] at this
  exact Subtype.ext this

variable (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)

lemma Th_rho (a : A) : Th e (rho hA he a) = e * a.1 := by
  apply mat_ext; intro v
  rw [Th_mulVec, rho_apply]
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hA _ a.2 _ he]

abbrev Fe : Subalgebra k (Module.End k (Wd e)) := (rho hA he).range

lemma map_Th_Fe : (Fe hA he).toSubmodule.map (Th e) = A.toSubmodule.map (LinearMap.mulLeft k e) := by
  ext m; constructor
  · rintro ⟨f, ⟨a, rfl⟩, rfl⟩
    exact ⟨a.1, a.2, by simp [Th_rho hA he]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨rho hA he ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, by simp [Th_rho hA he]⟩

lemma Fe_isField (hne : e ≠ 0)
    (hf : ∀ a ∈ A, e * a = 0 ∨ ∃ b ∈ A, e * a * b = e) : IsField (Fe hA he) := by
  have hW : ∃ v : Fin N → k, e *ᵥ v ≠ 0 := by
    by_contra h; push Not at h; exact hne (mat_ext fun v => by simp [h v])
  obtain ⟨v₀, hv₀⟩ := hW
  refine ⟨⟨0, 1, fun h => ?_⟩, ?_, ?_⟩
  · have := congrArg (fun x : Fe hA he => ((x.1 (Pe e v₀) : Wd e) : Fin N → k)) h
    change 0 = e *ᵥ v₀ at this
    exact hv₀ this.symm
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show rho hA he a * rho hA he b = rho hA he b * rho hA he a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA _ a.2 _ b.2)
  · rintro ⟨_, a, rfl⟩ hx
    have hea : e * a.1 ≠ 0 := by
      intro h0; apply hx; apply Subtype.ext
      ext w : 1; apply Subtype.ext
      obtain ⟨v, rfl⟩ := Pe_surj e w
      show a.1 *ᵥ (e *ᵥ v) = 0
      rw [Matrix.mulVec_mulVec, hA _ a.2 _ he, h0, Matrix.zero_mulVec]
    rcases hf a.1 a.2 with h0 | ⟨b, hb, hab⟩
    · exact absurd h0 hea
    refine ⟨⟨rho hA he ⟨b, hb⟩, ⟨b, hb⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    ext w : 1; apply Subtype.ext
    obtain ⟨v, rfl⟩ := Pe_surj e w
    show a.1 *ᵥ (b *ᵥ (e *ᵥ v)) = e *ᵥ v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, hA _ hb _ he, ← mul_assoc,
      hA _ a.2 _ he, hab]

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section

noncomputable section

open Matrix Module

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb

variable {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {N : ℕ}

theorem rank_eq_of_idem {R : Type*} [Field R] {P Q : Matrix (Fin N) (Fin N) R} (hP : P * P = P) (hQ : Q * Q = Q)
    (hu : IsUnit (Q * P + (1 - Q) * (1 - P)).det) : P.rank = Q.rank := by
  set u := Q * P + (1 - Q) * (1 - P)
  have h1 : u * P = Q * P := by
    simp only [u, add_mul, mul_assoc, sub_mul, one_mul, hP, sub_self, mul_zero, add_zero]
  have h2 : Q * u = Q * P := by
    simp only [u, mul_add, ← mul_assoc, mul_sub, mul_one, hQ, sub_self, zero_mul, add_zero]
  have : (u * P).rank = (Q * u).rank := by rw [h1, h2]
  rwa [rank_mul_eq_right_of_isUnit_det u P hu, rank_mul_eq_left_of_isUnit_det u Q hu] at this

theorem isClosed_idem_rank (n : ℕ) : IsClosed {P : Matrix (Fin N) (Fin N) k | P * P = P ∧ P.rank = n} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro Q hQ
  by_cases hi : Q * Q = Q
  · have hr : Q.rank ≠ n := fun h => hQ ⟨hi, h⟩
    refine ⟨{P | (Q * P + (1 - Q) * (1 - P)).det ≠ 0}, fun P hP hP' => hr ?_, ?_, ?_⟩
    · rw [← hP'.2]
      exact (rank_eq_of_idem hP'.1 hi (isUnit_iff_ne_zero.2 hP)).symm
    · exact isOpen_ne_fun (((continuous_const.mul continuous_id).add
        (continuous_const.mul (continuous_const.sub continuous_id))).matrix_det) continuous_const
    · show (Q * Q + (1 - Q) * (1 - Q)).det ≠ 0
      have : Q * Q + (1 - Q) * (1 - Q) = 1 := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, hi]; abel
      rw [this, det_one]; exact one_ne_zero
  · exact ⟨{P | P * P ≠ P}, fun P hP hP' => hP hP'.1, isOpen_ne_fun (continuous_id.mul continuous_id) continuous_id,
      hi⟩

theorem orbClosed_gen (N r : ℕ) (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (hA : IsReduced A)
    (b : Fin r → A) (hb : Submodule.span k (Set.range b) = ⊤) (ρ₀ : A →ₐ[k] Matrix (Fin N) (Fin N) k) :
    IsClosed {w : Fin r → Matrix (Fin N) (Fin N) k | ∃ g : GL (Fin N) k, ∀ i, w i = g.val * ρ₀ (b i) * g⁻¹.val} := by
  classical
  let L : (Fin r → k) → A := fun c => ∑ i, c i • b i
  let Φ : (Fin r → Matrix (Fin N) (Fin N) k) → (Fin r → k) → Matrix (Fin N) (Fin N) k :=
    fun w c => ∑ i, c i • w i
  have hL : ∀ a, ∃ c, L c = a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun k).1 (hb ▸ Submodule.mem_top)
  choose s hs using hL
  have Lsub : ∀ c c', L (c - c') = L c - L c' := fun c c' => by
    simp only [L, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have Φsub : ∀ w c c', Φ w (c - c') = Φ w c - Φ w c' := fun w c c' => by
    simp only [Φ, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have Φadd : ∀ w c c', Φ w (c + c') = Φ w c + Φ w c' := fun w c c' => by
    simp only [Φ, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have Φsmul : ∀ w (t : k) c, Φ w (t • c) = t • Φ w c := fun w t c => by
    simp only [Φ, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have Lsingle : ∀ i, L (Pi.single i 1) = b i := fun i => by
    simp [L, Pi.single_apply]
  have Φsingle : ∀ w i, Φ w (Pi.single i 1) = w i := fun w i => by
    simp [Φ, Pi.single_apply]
  have hΦc : ∀ c : Fin r → k, Continuous fun w : Fin r → Matrix (Fin N) (Fin N) k => Φ w c := fun c =>
    continuous_finsetSum _ fun i _ => (continuous_apply i).const_smul (c i)
  let S : Set (Fin r → Matrix (Fin N) (Fin N) k) :=
    (⋂ c, ⋂ (_ : L c = 0), {w | Φ w c = 0}) ∩ ((⋂ a, ⋂ a', {w | Φ w (s (a * a')) = Φ w (s a) * Φ w (s a')}) ∩
      ({w | Φ w (s 1) = 1} ∩ ⋂ e, ⋂ (_ : IsIdempotentElem e),
        (fun w => Φ w (s e)) ⁻¹' {P | P * P = P ∧ P.rank = (ρ₀ e).rank}))
  have hS : IsClosed S := by
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
    · exact isClosed_iInter fun c => isClosed_iInter fun _ => isClosed_eq (hΦc c) continuous_const
    · exact isClosed_iInter fun a => isClosed_iInter fun a' =>
        isClosed_eq (hΦc _) ((hΦc _).mul (hΦc _))
    · exact isClosed_eq (hΦc _) continuous_const
    · exact isClosed_iInter fun e => isClosed_iInter fun _ =>
        (isClosed_idem_rank (ρ₀ e).rank).preimage (hΦc (s e))
  convert hS using 1
  ext w
  simp only [S, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨g, hg⟩
    have hΦ : ∀ c, Φ w c = g.val * ρ₀ (L c) * g⁻¹.val := fun c => by

      simp only [Φ, L, hg, map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    have hgi : g⁻¹.val * g.val = 1 := Units.inv_mul g
    refine ⟨fun c hc => by rw [hΦ, hc, map_zero, mul_zero, zero_mul], fun a a' => ?_, ?_, fun e he => ?_⟩
    · rw [hΦ, hΦ, hΦ, hs, hs, hs, map_mul]
      simp only [mul_assoc]
      rw [← mul_assoc g⁻¹.val g.val, hgi, one_mul]
    · rw [hΦ, hs, map_one, mul_one, Units.mul_inv]
    · rw [hΦ, hs]
      refine ⟨?_, ?_⟩
      · have := congrArg ρ₀ he.eq
        rw [map_mul] at this
        simp only [mul_assoc]
        rw [← mul_assoc g⁻¹.val g.val, hgi, one_mul, ← mul_assoc (ρ₀ e), this]
      · rw [rank_mul_eq_left_of_isUnit_det _ _ (isUnits_det_units g⁻¹),
          rank_mul_eq_right_of_isUnit_det _ _ (isUnits_det_units g)]
  · rintro ⟨h0, hmul, h1, hrk⟩
    have hwd : ∀ c c', L c = L c' → Φ w c = Φ w c' := fun c c' h => by
      have := h0 (c - c') (by rw [Lsub, h, sub_self])
      rwa [Φsub, sub_eq_zero] at this
    let ρl : A →ₗ[k] Matrix (Fin N) (Fin N) k :=
      { toFun := fun a => Φ w (s a)
        map_add' := fun a a' => by
          rw [← Φadd]; apply hwd; rw [hs]
          simp only [L, Pi.add_apply, add_smul, Finset.sum_add_distrib]
          rw [show (∑ i, s a i • b i) = L (s a) from rfl, show (∑ i, s a' i • b i) = L (s a') from rfl, hs, hs]
        map_smul' := fun t a => by
          rw [RingHom.id_apply, ← Φsmul]; apply hwd; rw [hs]
          simp only [L, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
          rw [show (∑ i, s a i • b i) = L (s a) from rfl, hs] }
    let ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k := AlgHom.ofLinearMap ρl h1 hmul
    have hρ : ∀ a, ρ a = Φ w (s a) := fun _ => rfl
    obtain ⟨g, hg⟩ := orbHom_gen k N A hA ρ₀ ρ fun e he => by rw [hρ, (hrk e he).2]
    refine ⟨g, fun i => ?_⟩
    rw [← hg, hρ, ← Φsingle w i]
    apply hwd
    rw [hs, Lsingle]

end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
end
end
