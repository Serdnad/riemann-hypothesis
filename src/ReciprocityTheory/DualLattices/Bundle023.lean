module

public import ReciprocityTheory.DualLattices.Bundle019
public import ReciprocityTheory.DualLattices.Bundle020
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.DualLattices.Bundle016
public import ReciprocityTheory.DualLattices.Bundle014

@[expose] public section

section

noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)

theorem surjective_ainfTower_zero : Function.Surjective ((ainfTowerL p O hv ε hε).q 0).1 :=
  fun y => Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O) ^ (0 + 1)}) y

theorem ker_ainfTower_zero : RingHom.ker ((ainfTowerL p O hv ε hε).q 0).1 =
    Ideal.span {((p : ℕ) : ((ainfTowerL p O hv ε hε).O : Type))} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  have hq : ((ainfTowerL p O hv ε hε).q 0).1 a =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ (0 + 1)}) a := rfl
  rw [hq]
  exact (Ideal.Quotient.eq_zero_iff_dvd _ _).trans (by rw [pow_one]; rfl)

theorem ainf_zeta0 (h2 : p = 2) :
    (((ainfTowerL p O hv ε hε).ζ 0 : ((ainfTowerL p O hv ε hε).O : Type)ˣ) :
      ((ainfTowerL p O hv ε hε).O : Type)) = -1 := by
  have hz : (((ainfTowerL p O hv ε hε).ζ 0 : ((ainfTowerL p O hv ε hε).O : Type)ˣ) :
      ((ainfTowerL p O hv ε hε).O : Type)) = ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt := by
    show zetaV p O ε 0 = _
    simp [zetaV, root, fontaineTheta_teichmuller]
  rw [hz]
  clear hz
  haveI : NoZeroDivisors O :=
    hv.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  set z := ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt with hzdef
  clear_value z
  rw [h2] at hε
  exact hε.eq_neg_one_of_two_right

end ReciprocityTheory.PGsh.Be2
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.PullbackHopfOrder

private theorem restrict_red_surj {p : ℕ} [Fact p.Prime] {g : ℕ} (n : Nb p g) : ∃ t, red p g t = n := by
  refine ⟨fun i => ((n i).val : ℤ_[p]), funext fun i => ?_⟩
  simp [red]

private theorem restrict_red_mulVec {p : ℕ} [Fact p.Prime] {g : ℕ} (M : Matrix (Ix g) (Ix g) ℤ_[p])
    (t : TT p g) : red p g (M *ᵥ t) = M.map PadicInt.toZMod *ᵥ red p g t := by
  funext i

  simp [red, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem restrict_hopfOrder_length : RestrictedHopfOrderStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H a ha r Bw hrange hkerB d hd
  have hE : H.ρ a * H.ρ a = H.ρ a := by rw [← map_mul, ha]
  have hcol : ∀ j : Ix g, ∃ k : Fin r → ℤ_[p], Bw *ᵥ k = H.ρ a *ᵥ Pi.single j 1 := by
    intro j
    have hm : H.ρ a *ᵥ Pi.single j 1 ∈ LinearMap.range (Matrix.mulVecLin Bw) := by
      rw [hrange]
      exact ⟨Pi.single j 1, rfl⟩
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, hk⟩
  choose kk hkk using hcol
  let K : Matrix (Fin r) (Ix g) ℤ_[p] := Matrix.of fun i j => kk j i
  have hBK : Bw * K = H.ρ a := by
    ext i j
    have h1 : (Bw * K) i j = (Bw *ᵥ kk j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, K]
    rw [h1, hkk j]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hKB : K * Bw = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    apply LinearMap.ker_eq_bot.mp hkerB
    show Bw *ᵥ ((K * Bw) *ᵥ x) = Bw *ᵥ x
    obtain ⟨y, hy⟩ : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin (H.ρ a)) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBK, ← hy]
    show H.ρ a *ᵥ (H.ρ a *ᵥ y) = H.ρ a *ᵥ y
    rw [Matrix.mulVec_mulVec, hE]
  let ψ := psiW Bw
  let χ : Nb p g →+ (Fin r → ZMod p) := (Matrix.mulVecLin (K.map PadicInt.toZMod)).toAddMonoidHom
  have hχψ : ∀ x, χ (ψ x) = x := by
    intro x
    show K.map PadicInt.toZMod *ᵥ (Bw.map PadicInt.toZMod *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hKB, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hred : ∀ t, ψ (χ (red p g t)) = red p g (H.ρ a *ᵥ t) := by
    intro t
    show Bw.map PadicInt.toZMod *ᵥ (K.map PadicInt.toZMod *ᵥ red p g t) = _
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hBK, ← restrict_red_mulVec]
  have hA : ∀ f ∈ H.AA.carrier, (fun n => f (ψ (χ n))) ∈ H.AA.carrier := by
    intro f hf
    obtain ⟨f', hf', hff⟩ := H.h3 a f hf
    convert hf' using 1
    funext n
    obtain ⟨t, rfl⟩ := restrict_red_surj n
    rw [hff, hred]
  have hinj : Function.Injective ψ := fun x y h => by rw [← hχψ x, ← hχψ y, h]
  have hEE : H.ρL a * H.ρL a = H.ρL a := by rw [← map_mul, ha]
  let e := hd.some
  let Q1 : Matrix (Fin g) (Fin d) R :=
    LinearMap.toMatrix' ((LinearMap.range (H.ρL a).mulVecLin).subtype ∘ₗ e.symm.toLinearMap)
  let Q2 : Matrix (Fin d) (Fin g) R :=
    LinearMap.toMatrix' (e.toLinearMap ∘ₗ (H.ρL a).mulVecLin.rangeRestrict)
  have hQ12 : Q1 * Q2 = H.ρL a := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun x => ?_
    simp [Matrix.toLin'_apply]
  have hQ21 : Q2 * Q1 = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    refine LinearMap.ext fun y => ?_
    have hz : (H.ρL a).mulVecLin.rangeRestrict ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) =
        e.symm y := by
      apply Subtype.ext
      obtain ⟨w, hw⟩ := (e.symm y).2
      show H.ρL a *ᵥ ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) = e.symm y
      rw [← hw]
      show H.ρL a *ᵥ (H.ρL a *ᵥ w) = H.ρL a *ᵥ w
      rw [Matrix.mulVec_mulVec, hEE]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, LinearMap.id_apply]
    rw [hz, LinearEquiv.apply_symm_apply]
  have hF : Q2ᵀ * Q1ᵀ = (H.ρL a)ᵀ := by rw [← Matrix.transpose_mul, hQ12]
  have h21 : Q1ᵀ * Q2ᵀ = 1 := by rw [← Matrix.transpose_mul, hQ21, Matrix.transpose_one]
  obtain ⟨eO⟩ := omega_pull p ψ χ hχψ H.AA.carrier hA H.φ H.cotangent_surjective H.cotangent_ker_eq (H.ρL a)ᵀ Q2ᵀ Q1ᵀ hF h21
    (fun f f' l hff hl => H.cotangent_linear a f f' l (fun t => by rw [hff, hred]) hl)
  refine ⟨pullHopf ψ H.AA (isLat_pull v hS.integers ψ hinj H.AA), pullHopf_carrier _ _ _, ?_⟩
  rw [pullHopf_carrier]
  exact ⟨d, fun _ => (p : R), ⟨eO.trans (qPi p d)⟩, by simp [Finset.prod_const]⟩

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

structure Lifts {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal}
    {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O]
    [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) where
  κ : Ix g → Fin U.m
  card_phi : ∀ i, (Finset.univ.filter fun j => κ j = U.φ i).card =
    (Finset.univ.filter fun j => κ j = i).card
  r_zero : ∀ i, (∀ j, κ j ≠ i) → U.r i = 0
  Λ : Matrix (Ix g) (Ix g) R
  Λ_det : IsUnit Λ.det
  Λ_block : ∀ j, Matrix.vecMul (Λ j) (U.εT (κ j)) = Λ j
  ε : Ix g → R
  ε_ne : ∀ j, ε j ≠ 0
  ε_prod : ∀ i, ∏ j ∈ Finset.univ.filter (fun j => κ j = i), v (algebraMap R C (ε j)) = X i
  u : Ix g → Nb p g → C
  u_int : ∀ j y, v (u j y) ≤ 1
  u_cong : ∀ j (y : Nb p g), v (u j y - algebraMap R C (∑ k, Λ j k * ((y k).val : R))) < 1
  x_mem : ∀ j, (fun y => algebraMap R C (ε j) * u j y) ∈ augIdeal H.AA.carrier
  s : ℕ
  b : Fin s → O
  eig : ∀ j k (t : TT p g),
    u j (red p g (H.ρ (b k) *ᵥ t)) = algebraMap R C (U.sg (κ j) (b k)) * u j (red p g t)
  frobChar : ∀ j k, U.sg (U.φ (κ j)) (b k) = U.sg (κ j) (b k) ^ p
  sep : ∀ j j', κ j ≠ κ j' → ∃ k, v (algebraMap R C (U.sg (κ j) (b k) - U.sg (κ j') (b k))) = 1

def EigenLiftsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) → Nonempty (Lifts H U X)

def EigenLiftsBasisStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    ∏ i, X i = v (algebraMap R C cp) ^ g → ∀ D : Lifts H U X,
    H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val)

def EigenLiftsFrobeniusStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X),
    H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val) →
    ∀ i, X i ^ p ≤ X (U.φ i) * v (algebraMap R C (p : R)) ^ U.r (U.φ i)

theorem core_of (hL : EigenLiftsStatement) (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) :
    EigenLengthFrobeniusStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp hS H U X hX hprod i
  obtain ⟨D⟩ := hL p g C v R O σ cp hp hS H U X hX
  exact hF p g C v R O σ cp hp hS H U X D (hB p g C v R O σ cp hS H U X hprod D) i

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def EmbeddingSeparatingGroupStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H),
    ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (β : G → O),
      (∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) ∧ H.ρ (β 1) = 1 ∧
      IsUnit (Fintype.card G : R) ∧
      (∀ i γ, U.εT i ≠ 0 → U.sg (U.φ i) (β γ) = U.sg i (β γ) ^ p) ∧
      (∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
        ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1) ∧
      (∀ i, U.εT i ≠ 0 → ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1)

def EigenElementaryDivisorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) →
    ∃ (κ : Ix g → Fin U.m) (Λ : Matrix (Ix g) (Ix g) R) (ε : Ix g → R),
      IsUnit Λ.det ∧ (∀ j, Matrix.vecMul (Λ j) (U.εT (κ j)) = Λ j) ∧
      (∀ j, ∃ c, cp = ε j * c) ∧
      (∀ i, ∏ j ∈ Finset.univ.filter (fun j => κ j = i), v (algebraMap R C (ε j)) = X i) ∧
      (∀ i (n : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT i)) ≃ₗ[R] (Fin n → R)) →
        (Finset.univ.filter fun j => κ j = i).card = n) ∧
      (∀ i, Submodule.span R (Set.range fun k => (fromRows H.Ht (bt2 H U) * U.εT i) k) =
        Submodule.span R ((fun j => ε j • Λ j) '' {j | κ j = i}))

def EigenRankStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H),
    (∀ i, ∃ n : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT i)) ≃ₗ[R] (Fin n → R)) ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT (U.φ i))) ≃ₗ[R] (Fin n → R))) ∧
    (∀ i, U.εT i = 0 → U.r i = 0)

end ReciprocityTheory.PGsh.Up
end
end
