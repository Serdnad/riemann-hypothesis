module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import ReciprocityTheory.DualLattices.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
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
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

def PrismaticDieudonneAt {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : Prop :=
  ∃ (M : PDivGroup p O → ModuleCat.{0} (Ainf p O))
    (map : ∀ G H : PDivGroup p O, (G ⟶ H) →+ (M H →ₗ[Ainf p O] M G))
    (φ : ∀ G, M G →ₛₗ[(frobenius : Ainf p O →+* Ainf p O)] M G)
    (lie : ∀ G, M G →ₛₗ[fontaineTheta O p] G.dual.Lie)
    (dR : ∀ G, M G →ₛₗ[fontaineTheta O p] G.RigExt),
    (∀ G, Module.Free (Ainf p O) (M G) ∧ Module.Finite (Ainf p O) (M G) ∧
      Module.finrank (Ainf p O) (M G) = G.height ∧
      Function.Injective (φ G) ∧ (∀ m, ∃ n, φ G n = frobenius (xi ε) • m) ∧
      Module.Projective O G.dual.Lie ∧ Function.Surjective (lie G) ∧
      (∀ m, lie G m = 0 ↔ ∃ n, φ G m = frobenius (xi ε) • n) ∧
      Function.Surjective (dR G) ∧ (∀ m, dR G m = 0 ↔ ∃ n, m = xi ε • n) ∧
      map G G (𝟙 G) = LinearMap.id) ∧
    (∀ (G H K : PDivGroup p O) (f : G ⟶ H) (g : H ⟶ K),
      map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M H),
      map G H f (φ H m) = φ G (map G H f m) ∧
      lie G (map G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie H m) ∧
      dR G (map G H f m) = rigExtMap f (dR H m)) ∧
    (∀ G H : PDivGroup p O, Function.Injective (map G H) ∧
      ∀ u : M H →ₗ[Ainf p O] M G, (∀ m, u (φ H m) = φ G (u m)) → ∃ f, map G H f = u) ∧
    ∃ (l : M (PDivGroup.mu p O)) (e : M (const p O)),
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ l) ∧
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ e) ∧
      φ _ l = frobenius (xi ε) • l ∧ φ _ e = e ∧
      map _ _ (epsHom (zeta ε) hε.zeta_zero (zeta_succ_pow ε)) l = Sandwich.mu ε • e

def PrismaticDieudonne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C] [NormedAlgebra ℚ_[p] C]
    [CompleteSpace C] [IsAlgClosed C] (O : Type) [CommRing O] [Algebra O C],
    IsIntegers O C →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
      (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), PrismaticDieudonneAt hε

end GlobalTheory.Published
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

structure CycPerfd (p : ℕ) [Fact p.Prime] : Type 1 where
  R : Type
  [ring : CommRing R]
  [nonunit : Fact ¬IsUnit (p : R)]
  [complete : IsAdicComplete (span {(p : R)}) R]
  reg : IsSMulRegular R (p : R)
  ε : PreTilt R p
  zeta_zero : zeta ε 0 = 1
  surj : Function.Surjective (fontaineTheta R p)
  ker_eq : RingHom.ker (fontaineTheta R p) = span {xi ε}

attribute [instance] CycPerfd.ring CycPerfd.nonunit CycPerfd.complete

def CycPerfd.Over {p : ℕ} [Fact p.Prime] (S S' : CycPerfd p) [Algebra S.R S'.R] (α : Ainf p S.R →+* Ainf p S'.R) : Prop :=
  (∀ a, fontaineTheta S'.R p (α a) = algebraMap S.R S'.R (fontaineTheta S.R p a)) ∧
    (∀ a, α (frobenius a) = frobenius (α a)) ∧ α (teichmuller p S.ε) = teichmuller p S'.ε

def CycPerfd.ofIntegers (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) : CycPerfd p where
  R := O
  reg := fun a b h => sub_eq_zero.1 (ReciprocityTheory.PGsh.Ainf.torsion_free p O hv 1 _ (by
    have h' : (p : O) * a = (p : O) * b := h
    rw [pow_one, sub_mul, mul_comm a, mul_comm b, h', sub_self]))
  ε := ε
  zeta_zero := (zeta_succ_pow ε 0).symm.trans hε.pow_eq_one
  surj := ReciprocityTheory.PGsh.Ainf.theta_surj p O hv
  ker_eq := ReciprocityTheory.PGsh.Ainf.ker_theta p O hv ε hε


end GlobalTheory.Published
end
end

section

noncomputable section

open WittVector Ideal CategoryTheory Opposite Function

namespace GlobalTheory.DieudonneTest

open PDivGroup Sandwich Dieudonne

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

open WittVector Ideal CategoryTheory Opposite Function in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
private theorem exists_zmod_mul_of_pow_eq_pow_pred_mul {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} [Fact p.Prime] [CharP R p] {t x : R} (ht : t ≠ 0)
    (hx : x ^ p = t ^ (p - 1) * x) : ∃ k : ZMod p, x = ZMod.castHom (dvd_refl p) R k * t := by
  classical
  by_contra hne
  push_neg at hne
  have hp : p.Prime := Fact.out
  set Q : Polynomial R := Polynomial.X ^ p - Polynomial.C (t ^ (p - 1)) * Polynomial.X with hQ
  have hdeg : Q.natDegree = p := by
    rw [hQ, Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)) hp.one_lt
  have hQ0 : Q ≠ 0 := fun h0 => by
    rw [h0, Polynomial.natDegree_zero] at hdeg
    exact hp.ne_zero hdeg.symm
  have hroot : ∀ y, y ^ p = t ^ (p - 1) * y → y ∈ Q.roots := fun y hy => by
    rw [Polynomial.mem_roots hQ0, Polynomial.IsRoot, hQ]
    simp [hy]
  set f : ZMod p → R := fun k => ZMod.castHom (dvd_refl p) R k * t with hf_def
  have hf : Function.Injective f := fun k l hkl =>
    ZMod.castHom_injective R (mul_right_cancel₀ ht hkl)
  have htp : t ^ p = t ^ (p - 1) * t := by rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
  have hfroot : ∀ k, f k ^ p = t ^ (p - 1) * f k := by
    intro k
    simp only [hf_def, mul_pow, ← map_pow, ZMod.pow_card, htp]
    ring
  have hsub : insert x (Finset.univ.image f) ⊆ Q.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hroot _ hx
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hy
      exact hroot _ (hfroot k)
  have hnot : x ∉ Finset.univ.image f := fun hm => by
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hm
    exact hne k hk.symm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hf, Finset.card_univ,
    ZMod.card] at hcard
  have h2 := (Multiset.toFinset_card_le Q.roots).trans (Polynomial.card_roots' Q)
  omega


open WittVector Ideal CategoryTheory Opposite Function in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
theorem _root_.GlobalTheory.DieudonneTest.eigen_step [IsDomain (PreTilt O p)] {ε : PreTilt O p}
    (hε : IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p) {a : _root_.GlobalTheory.Sandwich.Ainf p O}
    (h : WittVector.frobenius a = WittVector.frobenius (_root_.GlobalTheory.Sandwich.xi ε) * a) :
    ∃ (c : ℤ) (b : _root_.GlobalTheory.Sandwich.Ainf p O), a = c * _root_.GlobalTheory.Sandwich.mu ε + p * b ∧
      WittVector.frobenius b = WittVector.frobenius (_root_.GlobalTheory.Sandwich.xi ε) * b := by
  have hp : p.Prime := Fact.out
  have hrp : _root_.GlobalTheory.Sandwich.root ε ^ p = ε := by
    unfold _root_.GlobalTheory.Sandwich.root
    exact frobeniusEquiv_symm_pow_p (PreTilt O p) p ε
  have hε1 : ε ≠ 1 := by
    intro h1
    have hr1 : _root_.GlobalTheory.Sandwich.root ε = 1 := by
      unfold _root_.GlobalTheory.Sandwich.root
      rw [h1, map_one]
    rw [hr1, map_one] at hε
    have h2 := hε.eq_orderOf
    rw [orderOf_one] at h2
    exact hp.one_lt.ne' h2
  set t : PreTilt O p := ε - 1 with ht_def
  have ht : t ≠ 0 := sub_ne_zero.2 hε1
  set s : PreTilt O p := ∑ i ∈ Finset.range p, _root_.GlobalTheory.Sandwich.root ε ^ i with hs
  have hst : s ^ p * t = t ^ p := by
    have h1 : (_root_.GlobalTheory.Sandwich.root ε - 1) * s = t := by rw [hs, mul_geom_sum, hrp]
    have h2 : (_root_.GlobalTheory.Sandwich.root ε - 1) ^ p = t := by rw [sub_pow_char, one_pow, hrp]
    calc s ^ p * t = ((_root_.GlobalTheory.Sandwich.root ε - 1) * s) ^ p := by rw [mul_pow, h2, mul_comm]
      _ = t ^ p := by rw [h1]
  have hsp : s ^ p = t ^ (p - 1) := by
    apply mul_right_cancel₀ ht
    rw [hst, ← pow_succ, Nat.sub_add_cancel hp.one_le]
  have hξ0 : WittVector.coeff (_root_.GlobalTheory.Sandwich.xi ε) 0 = s := by
    rw [← WittVector.constantCoeff_apply]
    unfold _root_.GlobalTheory.Sandwich.xi

    simp [map_sum, map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, hs]
  have hμ0 : WittVector.coeff (_root_.GlobalTheory.Sandwich.mu ε) 0 = t := by
    unfold _root_.GlobalTheory.Sandwich.mu
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
  have ha0 : WittVector.coeff a 0 ^ p = t ^ (p - 1) * WittVector.coeff a 0 := by
    have h3 := congrArg (fun x => WittVector.coeff x 0) h
    simp only [WittVector.mul_coeff_zero, WittVector.coeff_frobenius_charP, hξ0] at h3
    rw [h3, hsp]
  obtain ⟨k, hk⟩ := exists_zmod_mul_of_pow_eq_pow_pred_mul ht ha0
  refine ⟨(k.val : ℤ), ?_⟩
  set d : _root_.GlobalTheory.Sandwich.Ainf p O :=
    a - ((k.val : ℤ) : _root_.GlobalTheory.Sandwich.Ainf p O) * _root_.GlobalTheory.Sandwich.mu ε with hd
  have hd0 : WittVector.coeff d 0 = 0 := by
    rw [← WittVector.constantCoeff_apply, hd, map_sub, map_mul, map_intCast,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, hμ0, hk]
    simp
  have hφd : WittVector.frobenius d = WittVector.frobenius (_root_.GlobalTheory.Sandwich.xi ε) * d := by
    rw [hd, map_sub, map_mul, map_intCast, h, _root_.GlobalTheory.Dieudonne.frobenius_mu]
    ring
  have hpd : ∃ b : _root_.GlobalTheory.Sandwich.Ainf p O, d = (p : _root_.GlobalTheory.Sandwich.Ainf p O) * b := by
    by_cases hd00 : d = 0
    · exact ⟨0, by rw [hd00, mul_zero]⟩
    obtain ⟨m, b, hb0, hmb⟩ := WittVector.exists_eq_pow_p_mul d hd00
    cases m with
    | zero =>
      rw [pow_zero, one_mul] at hmb
      rw [hmb] at hd0
      exact absurd hd0 hb0
    | succ m => exact ⟨(p : _root_.GlobalTheory.Sandwich.Ainf p O) ^ m * b, by rw [hmb, pow_succ']; ring⟩
  obtain ⟨b, hb⟩ := hpd
  refine ⟨b, by rw [← hb, hd]; ring, ?_⟩
  have hp0 : (p : _root_.GlobalTheory.Sandwich.Ainf p O) ≠ 0 := WittVector.p_nonzero p _
  apply mul_left_cancel₀ hp0
  have h4 := hφd
  rw [hb, map_mul, map_natCast] at h4
  rw [h4]
  ring

end GlobalTheory.DieudonneTest
end
end

section

noncomputable section

namespace GlobalTheory.Published

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol
open scoped ENNReal

def TamagawaSpecialUnitary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ))
    [MeasurableSpace (realSU Ψ G)] [BorelSpace (realSU Ψ G)]
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E)
    (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)),
    2 ≤ r → Unr E → SelfDualLat G Λ →
    (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) →
    (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e →
    IsSReps G (Λ : Set (Fin r → E)) 1 s →
    Multipliable (locFactor E r) ∧
    (∑' j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G)
        (tangentHaar (realSU Ψ G) (formLie Ψ e))) *
      ENNReal.ofReal (|(discr (maximalRealSubfield E) : ℝ)| ^ (-((r : ℝ) ^ 2 - 1) / 2) *
        ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) *
        ∏' v, locFactor E r v) = 1

end GlobalTheory.Published
end
end

section

noncomputable section

namespace GlobalTheory.SUVol

open NumberField IsDedekindDomain MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

abbrev suReal (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : Subgroup (Ψ → GL (Fin r) ℂ) :=
  suGrp fun τ : Ψ => G.map τ.1

def suStab (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    Subgroup (suReal Ψ G) where
  carrier := {g | ∃ γ : GL (Fin r) E, IsUStab G Λ γ ∧ (γ : Matrix (Fin r) (Fin r) E).det = 1 ∧
    ∀ τ : Ψ, ((g.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1}
  one_mem' := ⟨1, ⟨by simp, by simp⟩, by simp, fun τ => by simp⟩
  mul_mem' := by
    rintro g h ⟨γ, ⟨g1, g2⟩, g3, g4⟩ ⟨δ, ⟨h1, h2⟩, h3, h4⟩
    refine ⟨γ * δ, ⟨fun x y => ?_, fun x => ?_⟩, by simp [g3, h3], fun τ => ?_⟩
    · rw [Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, g1, h1]
    · rw [Units.val_mul, ← mulVec_mulVec, ← g2, ← h2]
    · rw [Units.val_mul, Matrix.map_mul, ← g4, ← h4]; rfl
  inv_mem' := by
    rintro g ⟨γ, ⟨g1, g2⟩, g3, g4⟩
    have e : ∀ x, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) = x := by
      intro x
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have e1 : (γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨γ⁻¹, ⟨fun x y => ?_, fun x => ?_⟩, ?_, fun τ => ?_⟩
    · rw [← g1, e, e]
    · rw [g2 (_ *ᵥ x), e]
    · have := congrArg Matrix.det e1
      rwa [det_mul, g3, one_mul, det_one] at this
    · have e2 : ((g.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
          ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 = 1 := by
        rw [g4, ← Matrix.map_mul, e1]; simp
      exact Units.inv_eq_of_mul_eq_one_right e2


variable (E) in
def splitSign (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : ℝ :=
  if (v.asIdeal.primesOver (𝓞 E)).ncard = 2 then 1 else -1


variable (E) in
def localFactor (r : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : ℝ :=
  ∏ j ∈ Finset.Icc 2 r, (1 - splitSign E v ^ j / (Ideal.absNorm v.asIdeal : ℝ) ^ j)⁻¹

def archFactor (r : ℕ) : ℝ := ∏ j ∈ Finset.Ico 1 r, (j.factorial : ℝ) / (2 * Real.pi) ^ (j + 1)

end GlobalTheory.SUVol

namespace GlobalTheory.Published

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SUVol GlobalTheory.UCls

def PrasadVolumeSU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)),
    Unr E → SelfDualLat G Λ → (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) →
    (∃ (τ : E →+* ℂ) (x y : Fin r → ℂ), 0 < (hermC τ G x x).re ∧ (hermC τ G y y).re < 0) →
    ∃ ℰ : ℝ, HasProd (localFactor E r) ℰ ∧
      ∀ [MeasurableSpace (suReal Ψ G)] [BorelSpace (suReal Ψ G)] (m : Measure (suReal Ψ G)),
        IsCompactDualHaar (fun τ : Ψ => G.map τ.1) m →
        ∀ 𝓕 : Set (suReal Ψ G), IsFundamentalDomain (suStab Ψ G Λ) 𝓕 m →
          m 𝓕 = ENNReal.ofReal (|(discr (maximalRealSubfield E) : ℝ)| ^ (((r : ℝ) ^ 2 - 1) / 2) *
            archFactor r ^ fdeg E * ℰ)

end GlobalTheory.Published
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Raynaud

section Formal

variable {R : Type} [CommRing R] (I : Ideal R)

variable {I}

end Formal

section Parts

variable {S : Scheme.{0}}

variable {V : Type} [CommRing V]

theorem pow_eq_one_iff_of_isGrpPullback {S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G]
    [GrpObj G'] {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) {Y : Over S'} (y : Y ⟶ G') (n : ℕ) :
    pushPt h.1.w y ^ n = 1 ↔ y ^ n = 1 := by
  let m : (Y ⟶ G') →* (Over.mk (Y.hom ≫ f) ⟶ G) := MonoidHom.mk' (fun z => pushPt h.1.w z) fun a b =>
    Over.OverMorphism.ext (h.2 Y a b _ _ rfl rfl).symm
  have hm : Function.Injective m := fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  show m y ^ n = 1 ↔ _
  rw [← map_pow, map_eq_one_iff m hm]

end Parts

end GlobalTheory.Raynaud

namespace GlobalTheory.Published

open GlobalTheory.Raynaud IsLocalRing

end GlobalTheory.Published
end
end
