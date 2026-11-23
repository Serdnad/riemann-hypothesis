module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedMod (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) : Prop :=
  ∀ I : KH.Cell K ι 0, ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d,
    ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ) (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
      t ∈ KH.cellMon S I.1 ∧ IsMultiHomog t a ∧ (∀ j, IsMultiHomog (p j) a) ∧
      (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ t • x = ∑ j, p j • z j I

def H1GenAmple (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c →
      Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1) ∧ GeneratedMod S ι 𝓜 (e + c • N)

section Point

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]




omit [Fintype K] [∀ k, Subsingleton (ι k)] in
theorem isMultiHomog_one_zero : IsMultiHomog (1 : MRingOver S ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    rw [mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · exact h.symm
    · exact absurd rfl hm
  simp [this]

end Point

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def IsClosedMultiPt {S : Type*} [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (MRingOver S ι)) : Prop :=
  IsMultiProjPrime P ∧ ∀ Q : Ideal (MRingOver S ι), IsMultiProjPrime Q → P ≤ Q → Q = P

def GenNear (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ)
    (f : MRingOver S ι) (δ : K → ℕ) : Prop :=
  ∀ I : KH.Cell K ι 0, ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d,
    ∃ (n : ℕ) (t : MRingOver S ι) (a : K → ℕ) (r : ℕ) (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
      t ∈ KH.cellMon S I.1 ∧ IsMultiHomog t a ∧ (∀ j, IsMultiHomog (p j) (a + n • δ)) ∧
      (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ (f ^ n * t) • x = ∑ j, p j • z j I

def locIdealPart {S : Type*} [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (T : Submonoid (MRingOver S ι)) (P : Ideal (MRingOver S ι)) (d : K → ℤ) :
    Submodule S (LocalizedModule T M) :=
  Submodule.span S {w | ∃ (p : MRingOver S ι) (a : K → ℕ) (y : LocalizedModule T M), p ∈ P ∧ IsMultiHomog p a ∧
    y ∈ KH.locPart ι 𝓜 T (d - fun k => (a k : ℤ)) ∧ w = p • y}

section Point

end Point

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormPullback

theorem charZero_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun m hm => ?_
  have hmem : (m : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (m : ℤ)) = 0
    simp only [mConeMap, eq_intCast, Int.cast_natCast]
    rw [map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hm, map_zero]
  rw [hV.2.2.1, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

theorem isHomogeneous_of_map {σ : Type} {F : MvPolynomial σ ℤ} {m : ℕ}
    (h : (map (Int.castRingHom ℚ) F).IsHomogeneous m) : F.IsHomogeneous m := fun {d} hd =>
  h (by rw [coeff_map, eq_intCast, ne_eq, Int.cast_eq_zero]; exact hd)

theorem norm_prod_le_pow {B : ℝ} (hB : 0 ≤ B) (m : Multiset ℂ) (h : ∀ x ∈ m, ‖x‖ ≤ B) :
    ‖m.prod‖ ≤ B ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self a m)) (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))
      (norm_nonneg _) hB

theorem norm_last_le {n : ℕ} (a : ℕ → ℂ) (ha : a 0 = 1) {B : ℝ} (hB : 0 ≤ B)
    (hroot : ∀ w : ℂ, ∑ i ∈ Finset.range (n + 1), a i * w ^ (n - i) = 0 → ‖w‖ ≤ B) :
    ‖a n‖ ≤ B ^ n := by
  classical
  set p : Polynomial ℂ := ∑ i ∈ Finset.range (n + 1), Polynomial.C (a i) * Polynomial.X ^ (n - i) with hp
  have hcoeff : ∀ k, p.coeff k = ∑ i ∈ Finset.range (n + 1), if k = n - i then a i else 0 := by
    intro k
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
  have hdeg : p.natDegree ≤ n :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le n i)
  have hlead : p.coeff n = 1 := by
    rw [hcoeff, Finset.sum_eq_single 0]
    · simp [ha]
    · intro i hi hi0
      rw [Finset.mem_range] at hi
      rw [if_neg]
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  have hmon : p.Monic := Polynomial.monic_of_degree_le n (Polynomial.degree_le_of_natDegree_le hdeg) hlead
  have hnat : p.natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hlead]; exact one_ne_zero)
  have hzero : p.coeff 0 = a n := by
    rw [hcoeff, Finset.sum_eq_single n]
    · simp
    · intro i hi hin
      rw [Finset.mem_range] at hi
      rw [if_neg]
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : Multiset.card p.roots = n := by rw [Polynomial.splits_iff_card_roots.mp hsplit, hnat]
  have hprod := hsplit.coeff_zero_eq_prod_roots_of_monic hmon
  rw [hzero, hnat] at hprod
  rw [hprod, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← hcard]
  refine norm_prod_le_pow hB _ fun w hw => hroot w ?_
  have hw' := (Polynomial.mem_roots hmon.ne_zero).mp hw
  rw [Polynomial.IsRoot.def, hp, Polynomial.eval_finsetSum] at hw'
  simpa using hw'

end FibreNormPullback

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace BigIffGenDeg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ)) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (n : ℤ)) = 0
    rw [map_natCast C n, map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [h.2.2.1] at hmem
  exact_mod_cast (Ideal.mem_bot.mp hmem)

theorem coord_ne_zero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) :
    ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro k
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show mConeMap y (X ⟨k, i⟩) = 0
  simp [mConeMap, h0]

end BigIffGenDeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter

noncomputable section

theorem chartLat_le_chartLatNm {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) :
    chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have h := hs c hc
  rw [mem_integralClosure_iff]
  exact isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, h⟩)

theorem smallSectionCount_mono_lattice {Ω : Type*} [CommRing Ω] (P : ℕ → Ω → Prop) {La La' : ℕ → AddSubgroup Ω}
    (τ : ℕ) (hle : La τ ≤ La' τ) (hfin : {s : La' τ | P τ (s : Ω)}.Finite) :
    smallSectionCount P La τ ≤ smallSectionCount P La' τ := by
  unfold smallSectionCount
  have : Finite {s : La' τ // P τ (s : Ω)} := hfin.to_subtype
  have hc : Nat.card {s : La τ // P τ (s : Ω)} ≤ Nat.card {s : La' τ // P τ (s : Ω)} := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨⟨(s.1 : Ω), hle s.1.2⟩, s.2⟩ : {s : La' τ // P τ (s : Ω)})) ?_
    intro s t hst
    exact Subtype.ext (Subtype.ext (congrArg (fun u : {s : La' τ // P τ (s : Ω)} => ((u.1 : La' τ) : Ω)) hst))
  rcases Nat.eq_zero_or_pos (Nat.card {s : La τ // P τ (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hc)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedKleiman.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (d : ℕ)
    (M A : HermLine ι) (a : K → ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (A.a = fun k => (a k : ℤ)) → IsSemipositiveRel P0 P A → MonomialsBounded P A a → IsConjInvariantH A →
    ∀ j ≤ d, 0 ≤ II K ι P d (fun i : Fin d => if (i : ℕ) < j then M else A)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedKleiman.AtDim (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι))
    (M A : HermLine ι) (a : K → ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (A.a = fun k => (a k : ℤ)) → IsSemipositiveRel P0 P A → MonomialsBounded P A a → IsConjInvariantH A →
    ∀ j ≤ d, 0 ≤ II K ι P d (fun i : Fin d => if (i : ℕ) < j then M else A)

def MixedKleiman.LowAt (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι))
    (M A : HermLine ι) (a : K → ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (A.a = fun k => (a k : ℤ)) → IsSemipositiveRel P0 P A → MonomialsBounded P A a → IsConjInvariantH A →
    ∀ j < d, 0 ≤ II K ι P d (fun i : Fin d => if (i : ℕ) < j then M else A)

def MixedKleiman.TopAt (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι))
    (M : HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    0 ≤ II K ι P d (fun _ => M)

theorem MixedKleiman.atDim_zero : MixedKleiman.AtDim 0 := by
  intro K _ ι _ P P0 M A a II _ h1
  exact absurd h1 (by norm_num)

def MixedKleimanLow.Statement : Prop :=
  ∀ d : ℕ, MixedKleiman.AtDim (d - 1) → MixedKleiman.LowAt d

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SectionOrderAtPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (s : Ω) (W : Ideal (MRing ι)) (G H : MRing ι)
    (dg dh : K → ℕ),
    IsArithVar W 1 → mCoordIdeal y ≤ W → s ∈ chartLatNm y a τ →
    IsMultiHomog G dg → IsMultiHomog H dh → (∀ k, (dg k : ℤ) = dh k + τ * a k) →
    aeval y G = s * aeval y H → G ∉ W → H ∉ W →
    ∀ V ∈ divSupp W H, V ∈ divSupp W G ∧
      multAt (W ⊔ Ideal.span {H}) V ≤ multAt (W ⊔ Ideal.span {G}) V

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def BirationalModelExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ),
    IsArithVar P d → ∃ (Ω : Type) (_ : Field Ω) (y : (Σ k, ι k) → Ω), mCoordIdeal y = P ∧ Birational y

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SmallSectionPointHeight.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (τ : ℕ) (s : Ω) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    1 ≤ τ → s ∈ chartLatNm y A.a τ → s ≠ 0 → IsSmallH (mCoordIdeal y) y A τ s →
    ∃ f : MRing ι, (∃ d, IsMultiHomog f d) ∧ f ∉ mCoordIdeal y ∧
      ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal y ≤ W → f ∉ W → 0 ≤ II K ι W 1 ![A]

theorem SmallSectionPointHeight.chartLat_le_chartLatNm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have h := hs c hc
  exact (mem_integralClosure_iff _ _).mpr (isIntegral_algebraMap (x := (⟨_, h⟩ : chartRingZ y c)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def ChartPrimePowerInverse.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ p : ℕ, p.Prime → ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
      ∃ M : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
        (p : Ω) ^ M * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
          Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
            Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹})

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (df : K → ℕ) (f : MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    IsMultiHomog f df → f ∉ mCoordIdeal y →
    ∃ (n c : ℕ) (B : ℝ) (G : MvPolynomial (Fin (D + 1)) ℤ)
      (Fib : (Fin (D + 1) → ℂ) → Finset ((Σ k, ι k) → ℂ)),
      1 ≤ n ∧ 1 ≤ B ∧ G ≠ 0 ∧
      (∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
        ∀ z ∈ Fib ζ, z ∈ mcPts (mCoordIdeal y) ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0) ∧
      ∀ τ : ℕ, ∀ u ∈ chartLatNm y A.a τ, u ≠ 0 →
        ∃ F : MvPolynomial (Fin (D + 1)) ℤ, F ≠ 0 ∧ (∀ i, F.degreeOf i ≤ c * (τ + 1)) ∧
          ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
          ∀ M : ℝ, 0 ≤ M →
            (∀ z ∈ Fib ζ, ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
              (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧ aeval y g = u * aeval y h ∧
              eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
              ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
                M * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖) →
            ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * M ^ n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
