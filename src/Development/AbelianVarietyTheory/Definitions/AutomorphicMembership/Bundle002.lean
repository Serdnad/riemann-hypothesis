module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Mathlib.RingTheory.Nilpotent.Exp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle072
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PrimInIffSubsingleton
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalRingCardinality.DataHost
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
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

section

noncomputable section
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per
variable {l : ℕ} [Fact l.Prime]

def ringsOf (C : Core l) : LocRings l :=
  letI aU : Algebra ↥(MaximalUnramifiedExtension l) (Per.Bcris l) := C.u.toAlgebra
  letI aQ : Algebra ℚ_[l] (Per.Bcris l) := (C.u.comp (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))).toAlgebra
  letI aO : Algebra (Om l) (Per.BdR l) := ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o).toAlgebra
  letI aQ' : Algebra ℚ_[l] (Per.BdR l) :=
    (((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o).comp (algebraMap ℚ_[l] (Om l))).toAlgebra
  { B := Per.Bcris l
    BdR := Per.BdR l
    aQB := aQ
    aUB := aU
    tUB := IsScalarTower.of_algebraMap_eq fun _ => rfl
    aOdR := aO
    aQdR := aQ'
    tQdR := IsScalarTower.of_algebraMap_eq fun _ => rfl }

def eB (C : Core l) : (ringsOf C).B ≃+* Per.Bcris l := RingEquiv.refl (Per.Bcris l)

def eD (C : Core l) : (ringsOf C).BdR ≃+* Per.BdR l := RingEquiv.refl (Per.BdR l)

structure IsRealPD (C : Core l) (K : FinExt l)
    (PD : WeaklyAdmissibleFiltrations.PeriodData ↥(GK K) ℚ_[l] ↥(K0 K) ↥K.1 (ringsOf C).B (ringsOf C).BdR) : Prop where
  p : PD.p = l
  actB : ∀ g b, eB C (PD.actB g b) = Per.σB (g : GQ l) (eB C b)
  actdR : ∀ g b, eD C (PD.actdR g b) = Per.σD (g : GQ l) (eD C b)
  φ : ∀ b, eB C (PD.φ b) = Per.φB l (eB C b)
  ι : ∀ b, eD C (PD.ι b) = C.ι (eB C b)
  t : eB C PD.t = algebraMap (Per.Acris l) (Per.Bcris l) C.t
  χ : ∀ g, ((PD.χ g : ℚ_[l]ˣ) : ℚ_[l]) = ((C.χ (g : GQ l) : ℤ_[l]) : ℚ_[l])
  fil : ∀ a x, x ∈ PD.Fil a ↔ eD C x ∈ Per.FilD l a
  σ : ∀ (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) = (x : Om l) →
    ((PD.σ x : ↥(K0 K)) : Om l) = ((C.σ c : ↥(MaximalUnramifiedExtension l)) : Om l)

end GlobalTheory.MemLoc
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module

namespace GlobalTheory.WeilDeligne

section Exp

open IsNilpotent

theorem semiconj_exp {R : Type*} [Ring R] [Algebra ℚ R] {x a b : R} (ha : IsNilpotent a)
    (hb : IsNilpotent b) (hx : x * a = b * x) : x * exp a = exp b * x := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨k, hk⟩ := hb
  rw [exp_eq_sum (pow_eq_zero_of_le (le_max_left m k) hm),
    exp_eq_sum (pow_eq_zero_of_le (le_max_right m k) hk), Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, (SemiconjBy.pow_right (a := x) hx i).eq]

variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

theorem exp_add_smul {N : Matrix n n K} (hN : IsNilpotent N) (s t : K) :
    exp ((s + t) • N) = exp (s • N) * exp (t • N) := by
  rw [add_smul]
  exact exp_add_of_commute (((Commute.refl N).smul_left s).smul_right t) (hN.smul s) (hN.smul t)

theorem exp_smul_mul {N : Matrix n n K} (hN : IsNilpotent N) (s : K) :
    exp (s • N) * N = N * exp (s • N) :=
  (semiconj_exp (hN.smul s) (hN.smul s) ((Commute.refl N).smul_right s).eq).symm

theorem eq_of_exp_smul_eq {N N' : Matrix n n K} (hN : IsNilpotent N) (hN' : IsNilpotent N')
    {c : K} (hc : c ≠ 0) (H : ∀ k : ℕ, exp (((k : K) * c) • N) = exp (((k : K) * c) • N')) :
    N = N' := by
  obtain ⟨m, hm⟩ := hN
  obtain ⟨m', hm'⟩ := hN'
  ext i j
  let P : Matrix n n K → K[X] := fun M =>
    ∑ d ∈ Finset.range (m + m' + 2), monomial d ((d.factorial : K)⁻¹ * (M ^ d) i j)
  have hP : ∀ M : Matrix n n K, M ^ (m + m' + 2) = 0 → ∀ s : K,
      (P M).eval s = (exp (s • M)) i j := by
    intro M hM s
    rw [exp_eq_sum (k := m + m' + 2) (by rw [_root_.smul_pow, hM, smul_zero]), eval_finsetSum,
      Matrix.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eval_monomial, _root_.smul_pow, Matrix.smul_apply, Matrix.smul_apply, Rat.smul_def]
    simp only [smul_eq_mul]
    push_cast; ring
  have hPP : P N = P N' := by
    refine eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ => (k : K) * c) (fun a b hab => by simpa [hc] using hab) fun k => ?_)
    show _ = _
    rw [hP N (pow_eq_zero_of_le (by omega) hm), hP N' (pow_eq_zero_of_le (by omega) hm'), H]
  have := congrArg (fun p : K[X] => p.coeff 1) hPP
  simpa only [P, finsetSum_coeff, coeff_monomial_apply, Finset.sum_ite_eq',
    Finset.mem_range, show 1 < m + m' + 2 by omega, if_true, Nat.factorial_one,
    Nat.cast_one, inv_one, one_mul, pow_one] using this

end Exp

theorem charpoly_eq_of_isNilpotent_sub {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {f g : End K V} (hc : Commute f g)
    (hn : IsNilpotent (g - f)) : f.charpoly = g.charpoly := by
  refine eq_of_infinite_eval_eq _ _ ((f.charpoly.finite_setOfPred_isRoot
    (LinearMap.charpoly_monic f).ne_zero).infinite_compl.mono fun t ht => ?_)
  have hu : IsUnit (algebraMap K (End K V) t - f) := by
    rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.eval_charpoly]
    exact isUnit_iff_ne_zero.mpr ht
  obtain ⟨u, hu⟩ := hu
  have h1 : Commute (u : End K V) (g - f) := by
    rw [hu]
    exact (Algebra.commute_algebraMap_left t _).sub_left (hc.sub_right (Commute.refl f))
  have h2 : IsNilpotent ((↑u⁻¹ : End K V) * (g - f)) :=
    h1.units_inv_left.isNilpotent_mul_left hn
  have h3 : LinearMap.det (1 - (↑u⁻¹ : End K V) * (g - f)) = 1 := by
    have := LinearMap.eval_charpoly ((↑u⁻¹ : End K V) * (g - f)) 1
    rw [h2.charpoly_eq_X_pow_finrank, map_one] at this
    simpa using this.symm
  have h4 : algebraMap K (End K V) t - g = u * (1 - (↑u⁻¹ : End K V) * (g - f)) := by
    rw [mul_sub, Units.mul_inv_cancel_left, mul_one, hu]; abel
  show _ = _
  rw [LinearMap.eval_charpoly, LinearMap.eval_charpoly, h4, map_mul, h3, mul_one, hu]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def IsFrobSS (ρ : Weil h → End ℂ V) (N : End ℂ V) (a : WDRep h V) : Prop :=
  a.N = N ∧ ∀ g, Commute (a.ρ g) (ρ g) ∧ IsNilpotent (ρ g - a.ρ g)

theorem isFrobSS_self (a : WDRep h V) : IsFrobSS a.ρ a.N a :=
  ⟨rfl, fun g => ⟨Commute.refl _, by simp⟩⟩

theorem IsFrobSS.ρ_eq {ρ : Weil h → End ℂ V} {N : End ℂ V} {a : WDRep h V} (ha : IsFrobSS ρ N a)
    {g : Weil h} (hg : (ρ g).IsSemisimple) : a.ρ g = ρ g :=
  (End.isNilpotent_isSemisimple_unique (ha.2 g).2 (a.semisimple g) IsNilpotent.zero hg
    ((ha.2 g).1.symm.sub_left (Commute.refl _)) (Commute.zero_left _) (by simp)).2

theorem IsFrobSS.ρ_unique {ρ : Weil h → End ℂ V} {N N' : End ℂ V} {a b : WDRep h V}
    (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ N' b) : a.ρ = b.ρ :=
  MonoidHom.ext fun g =>
    (End.isNilpotent_isSemisimple_unique (ha.2 g).2 (a.semisimple g) (hb.2 g).2 (b.semisimple g)
      ((ha.2 g).1.symm.sub_left (Commute.refl _)) ((hb.2 g).1.symm.sub_left (Commute.refl _))
      (by simp)).2

theorem IsFrobSS.iso {ρ : Weil h → End ℂ V} {N : End ℂ V} {a : WDRep h V} {ρ' : Weil h → End ℂ V'}
    {N' : End ℂ V'} {b : WDRep h V'} (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ' N' b)
    (e : V ≃ₗ[ℂ] V') (hρ : ∀ g v, e (ρ g v) = ρ' g (e v)) (hN : ∀ v, e (N v) = N' (e v)) :
    a.Iso b := by
  have h1 : ∀ g, ρ' g = e.conjAlgEquiv ℂ (ρ g) := fun g => LinearMap.ext fun v => by
    simp [hρ]
  have h2 : IsFrobSS ρ' (a.transport e).N (a.transport e) := ⟨rfl, fun g => by
    rw [h1]
    refine ⟨(ha.2 g).1.map (e.conjAlgEquiv ℂ), ?_⟩
    have := (ha.2 g).2.map (e.conjAlgEquiv ℂ)
    rwa [map_sub] at this⟩
  refine ⟨e, fun g v => ?_, fun v => by rw [ha.1, hb.1, hN]⟩
  rw [← h2.ρ_unique hb]
  show _ = e.conjAlgEquiv ℂ (a.ρ g) (e v)
  simp

theorem IsFrobSS.iso_of_smul {ρ : Weil h → End ℂ V} {N : End ℂ V} {a b : WDRep h V} {c : ℂ}
    (hc : c ≠ 0) (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ (c • N) b) : a.Iso b :=
  WDRep.iso_of_N_eq_smul E Ω A w h V a b c hc (ha.ρ_unique hb) (by rw [hb.1, ha.1])

theorem isFrobSS_of_unipotent {ρ : Weil h → End ℂ V} {a : WDRep h V} (u : (End ℂ V)ˣ)
    (hu : IsNilpotent ((u : End ℂ V) - 1)) (hc : ∀ g, Commute (u : End ℂ V) (ρ g))
    (hρ : ∀ g, ρ g = a.ρ g * ((u ^ deg g : (End ℂ V)ˣ) : End ℂ V)) : IsFrobSS ρ a.N a := by
  refine ⟨rfl, fun g => ?_⟩
  obtain ⟨h1, h2⟩ := FrobSemisimpleUnique.nilpotent_part (u ^ deg g)
    (FrobSemisimpleUnique.isNilpotent_zpow_sub_one u hu _) ((hc g).units_zpow_left _) (hρ g)
  exact ⟨by simpa using (h2.add_left (Commute.refl _)).symm, h1⟩

theorem exists_isFrobSS (ρ : Representation ℂ (Weil h) V) (N : End ℂ V) (hρ : IsSmooth ρ)
    (hN : IsNilpotent N) (hc : ∀ g, ρ g * N = ((normV w : ℕ) : ℂ) ^ deg g • (N * ρ g)) :
    ∃ a : WDRep h V, IsFrobSS ρ N a := by
  obtain ⟨a, u, h1, h2, -, h3, h4⟩ :=
    exists_frobenius_semisimplification E Ω A w h V ρ N hρ hN hc
  exact ⟨a, h1 ▸ isFrobSS_of_unipotent u h2 h3 h4⟩

theorem IsFrobSS.charpoly_eq {ρ : Weil h → End ℂ V} {N : End ℂ V} {a : WDRep h V}
    (ha : IsFrobSS ρ N a) (g : Weil h) : (a.ρ g).charpoly = (ρ g).charpoly :=
  charpoly_eq_of_isNilpotent_sub (ha.2 g).1 (ha.2 g).2

theorem IsFrobSS.ρ_ineIncl {ρ : Representation ℂ (Weil h) V} {N : End ℂ V} {a : WDRep h V}
    (ha : IsFrobSS ρ N a) (hρ : IsSmooth ρ) (σ : Ine (F := E) A) :
    a.ρ (ineIncl h σ) = ρ (ineIncl h σ) := by
  refine ha.ρ_eq ?_
  have := compactSpace_Ine (E := E) A
  have : Finite (Ine (F := E) A ⧸ (ρ.comp (ineIncl h)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hρ
  obtain ⟨d, hd, -, hσ⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := (ρ.comp (ineIncl h)).ker)) σ
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ d - C 1)
    (separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr hd.ne') one_ne_zero).squarefree ?_
  rw [MonoidHom.mem_ker, map_pow] at hσ
  simpa [sub_eq_zero] using hσ

end GlobalTheory.WeilDeligne
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

section Defs

variable {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)

def Col (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun Λ Λ' : FrameLats σ J P => ∃ s, InS σ J P s ∧ latMap s Λ.1 = Λ'.1

def Col.lat {σ : E →+* E} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E} (c : Col σ J P) :
    Submodule (𝓞 E) (Fin n → E) := (Quot.out c).1

def FrCls (T' : E) (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun A B : {A // admitted σ J T' g Λ P A} => Move σ J Λ P A.1 B.1

def Term (T' : E) (g : ℕ) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Σ c : Col σ J P, FrCls σ J T' g c.lat P



variable {σ J} {T' : E} {g : ℕ} {P : Matrix (Fin n) (Fin (r + 1)) E}

namespace Term

variable (t : Term σ J T' g P)

end Term

end Defs

section Basic

variable {E : Type} [Field E] [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {T T' : E} {P A B : Matrix (Fin n) (Fin (r + 1)) E} {Λ : Submodule (𝓞 E) (Fin n → E)}






namespace Term

variable (t : Term σ J T' g P)

variable {t}

variable (t)

end Term

end Basic

section Examples

variable {E : Type} [Field E] [NumberField E]

end Examples

section Spaces

open Formalism.BasicNotions

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def coMat (V : HSpace E) {a : Type} (x : a → V.V) : Matrix (Fin V.rank) a E :=
  Matrix.of fun i b => V.frame.repr (x b) i

theorem hT_eq_sum (V : HSpace E) (x y : V.V) :
    V.hT x y = ∑ j, (∑ i, star (V.frame.repr x i) * V.gram i j) * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  RingHom.id_apply, HSpace.gram, starRingEnd_apply, mul_comm]

end Spaces

section Record

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

variable {D} {u u' : D.what₂.Word}

end Record

end GlobalTheory.IntTerm
end
end
