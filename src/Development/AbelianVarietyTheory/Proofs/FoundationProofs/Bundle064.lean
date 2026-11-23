module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle029
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

noncomputable section

namespace GlobalTheory.AlmostEt

variable {A S M : Type} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

def trTwist (tr : S → S) {n : ℕ} (a b : Fin n → S) (D : S → M) (x : S) : M :=
  ∑ i, a i • D (tr (b i * x))

def trTwistDefect (tr : S → S) {n : ℕ} (a b : Fin n → S) (D : S → M) (x u : S) : M :=
  trTwist tr a b D (x * u) - x • trTwist tr a b D u

def trExtDer (tr : S → S) {n : ℕ} (a b : Fin n → S) (e : S) (D : S → M) (y : S) : M :=
  e • ∑ j, b j • trTwistDefect tr a b D y (a j)

variable {B C : Subalgebra A S} {tr : S → S} {n : ℕ} {a b : Fin n → S} {e : S} {D : S → M}

theorem trTwist_add (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x y : S} (hx : x ∈ C)
    (hy : y ∈ C) : trTwist tr a b D (x + y) = trTwist tr a b D x + trTwist tr a b D y := by
  unfold trTwist
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := C.mul_mem (h.b_mem i) hx
  have h2 := C.mul_mem (h.b_mem i) hy
  rw [mul_add, h.tr_add _ h1 _ h2, hD.add _ (h.tr_mem _ h1) _ (h.tr_mem _ h2), smul_add]

theorem trTwist_smul (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {β x : S} (hβ : β ∈ B)
    (hx : x ∈ C) : trTwist tr a b D (β * x) = β • trTwist tr a b D x + (e * x) • D β := by
  unfold trTwist
  have key : ∀ i, a i • D (tr (b i * (β * x))) =
      β • (a i • D (tr (b i * x))) + (a i * tr (b i * x)) • D β := by
    intro i
    have h1 := C.mul_mem (h.b_mem i) hx
    have hm : b i * (β * x) = β * (b i * x) := by ring
    rw [hm, h.tr_mul _ hβ _ h1, hD.mul _ hβ _ (h.tr_mem _ h1), smul_add, mul_smul, smul_comm (a i) β]
  simp_rw [key, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul, h.left x hx]

theorem trTwist_zero (h : IsTrData B C tr a b e) (hD : IsDerOn B D) :
    trTwist tr a b D (0 : S) = 0 := by
  have := trTwist_add h hD C.zero_mem C.zero_mem
  rw [add_zero] at this
  simpa using this

theorem defect_add (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x u v : S} (hx : x ∈ C)
    (hu : u ∈ C) (hv : v ∈ C) :
    trTwistDefect tr a b D x (u + v) = trTwistDefect tr a b D x u + trTwistDefect tr a b D x v := by
  unfold trTwistDefect
  rw [mul_add, trTwist_add h hD (C.mul_mem hx hu) (C.mul_mem hx hv), trTwist_add h hD hu hv, smul_add]
  abel

theorem defect_zero (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x : S} (hx : x ∈ C) :
    trTwistDefect tr a b D x 0 = 0 := by
  unfold trTwistDefect
  rw [mul_zero, trTwist_zero h hD, smul_zero, sub_zero]

theorem defect_smul (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x β u : S} (hx : x ∈ C)
    (hβ : β ∈ B) (hu : u ∈ C) :
    trTwistDefect tr a b D x (β * u) = β • trTwistDefect tr a b D x u := by
  unfold trTwistDefect
  have hm : x * (β * u) = β * (x * u) := by ring
  rw [hm, trTwist_smul h hD hβ (C.mul_mem hx hu), trTwist_smul h hD hβ hu, smul_add, smul_sub,
    smul_smul x (e * u), smul_comm x β]
  have : x * (e * u) = e * (x * u) := by ring
  rw [this]
  abel

theorem defect_sum (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x : S} (hx : x ∈ C)
    (c : Fin n → S) (hc : ∀ i, c i ∈ B) :
    trTwistDefect tr a b D x (∑ i, c i * a i) = ∑ i, c i • trTwistDefect tr a b D x (a i) := by
  have : ∀ s : Finset (Fin n), trTwistDefect tr a b D x (∑ i ∈ s, c i * a i) =
      ∑ i ∈ s, c i • trTwistDefect tr a b D x (a i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using defect_zero h hD hx
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        defect_add h hD hx (C.mul_mem (h.le (hc j)) (h.a_mem j))
          (C.sum_mem fun i _ => C.mul_mem (h.le (hc i)) (h.a_mem i)),
        defect_smul h hD hx (hc j) (h.a_mem j), ih]
  exact this Finset.univ

theorem defect_mul (x y u : S) :
    trTwistDefect tr a b D (x * y) u =
      trTwistDefect tr a b D x (y * u) + x • trTwistDefect tr a b D y u := by
  unfold trTwistDefect
  rw [smul_sub, mul_assoc, mul_smul]
  abel

theorem trExtDer_swap (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x y : S} (hx : x ∈ C)
    (hy : y ∈ C) : y • trExtDer tr a b e D x =
      e • ∑ j, b j • trTwistDefect tr a b D x (y * a j) := by

  have step1 : ∀ j, e • (b j • trTwistDefect tr a b D x (y * a j)) =
      ∑ i, (tr (b i * (y * a j)) * b j) • trTwistDefect tr a b D x (a i) := by
    intro j
    have hya := C.mul_mem hy (h.a_mem j)
    have hl : e * (y * a j) = ∑ i, tr (b i * (y * a j)) * a i := by
      rw [← h.left _ hya]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [smul_comm, ← defect_smul h hD hx h.e_mem hya, hl,
      defect_sum h hD hx _ fun i => h.tr_mem _ (C.mul_mem (h.b_mem i) hya), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm (b j)]
  rw [Finset.smul_sum]
  simp_rw [step1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hr : ∀ i, ∑ j, tr (b i * (y * a j)) * b j = y • (e • b i) := by
    intro i
    have := h.right _ (C.mul_mem (h.b_mem i) hy)
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm y e, mul_assoc, mul_comm y (b i), ← this]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]; congr 2; ring
  simp_rw [hr]
  unfold trExtDer
  rw [Finset.smul_sum, Finset.smul_sum]
  simp_rw [smul_smul, smul_eq_mul, mul_assoc]

theorem trExtDer_isDerOn (h : IsTrData B C tr a b e) (hD : IsDerOn B D) :
    IsDerOn C (trExtDer tr a b e D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    unfold trExtDer
    rw [← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold trTwistDefect
    rw [← smul_add, add_mul, trTwist_add h hD (C.mul_mem hx (h.a_mem j)) (C.mul_mem hy (h.a_mem j)),
      add_smul]
    congr 1
    abel
  · intro x hx y hy
    have e1 : trExtDer tr a b e D (x * y) =
        e • ∑ j, b j • trTwistDefect tr a b D x (y * a j) + x • trExtDer tr a b e D y := by
      unfold trExtDer
      simp_rw [defect_mul, smul_add, Finset.sum_add_distrib, smul_add]
      congr 1
      rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_comm (b j) x, smul_comm e x]
    rw [e1, ← trExtDer_swap h hD hx hy, add_comm]
  · intro c
    unfold trExtDer
    have hc : algebraMap A S c ∈ B := B.algebraMap_mem c
    have : ∀ j, b j • trTwistDefect tr a b D (algebraMap A S c) (a j) =
        (b j * (e * a j)) • D (algebraMap A S c) := by
      intro j
      unfold trTwistDefect
      rw [trTwist_smul h hD hc (h.a_mem j), add_sub_cancel_left, smul_smul]
    simp [this, hD.alg c]

theorem trExtDer_apply_of_mem (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {β : S} (hβ : β ∈ B) :
    trExtDer tr a b e D β = (e ^ 3) • D β := by
  unfold trExtDer
  have : ∀ j, b j • trTwistDefect tr a b D β (a j) = (b j * (e * a j)) • D β := by
    intro j
    unfold trTwistDefect
    rw [trTwist_smul h hD hβ (h.a_mem j), add_sub_cancel_left, smul_smul]
  simp_rw [this, ← Finset.sum_smul, smul_smul]
  have hs : ∑ j, b j * (e * a j) = e * e := by
    rw [← h.sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]; congr 1; ring

theorem exists_derOn_ext : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn B D →
      ∃ D' : S → M, IsDerOn C D' ∧ ∀ β ∈ B, D' β = (e ^ 3) • D β := by
  intro A S M _ _ _ _ _ B C tr n a b e h D hD
  exact ⟨trExtDer tr a b e D, trExtDer_isDerOn h hD, fun β hβ => trExtDer_apply_of_mem h hD hβ⟩

end GlobalTheory.AlmostEt
end
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory

theorem towerAlg_mem_iff (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (s : (integralClosure (O0 p) Ω)) :
    s ∈ towerAlg T ↔ (s : Ω) ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  have himg : ((integralClosure (O0 p) Ω).val : integralClosure (O0 p) Ω → Ω) ''
      (Set.range (zS T) ∪ Set.range (qS T)) = Set.range T.ζ ∪ Set.range T.qq := by
    rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
    rfl
  have hmap : (towerAlg T).map (integralClosure (O0 p) Ω).val =
      Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
    rw [towerAlg, AlgHom.map_adjoin, himg]
  rw [← hmap, Subalgebra.mem_map]
  constructor
  · intro h; exact ⟨s, h, rfl⟩
  · rintro ⟨t, ht, hts⟩
    have : t = s := Subtype.ext hts
    exact this ▸ ht

end GlobalTheory
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem agree_div_apply {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (i j : Fin n) (u : kˣ)
    (hu : valuation k (u : k) = 1) : (ψ i / ψ j) u = (ω i / ω j) u := by
  simp only [MonoidHom.div_apply, h i u hu, h j u hu]

theorem agree_triv_iff {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (i j : Fin n) (x : k) :
    Triv (ψ i / ψ j) x ↔ Triv (ω i / ω j) x := by
  constructor
  · intro H u hu hx
    rw [← agree_div_apply h i j u hu]
    exact H u hu hx
  · intro H u hu hx
    rw [agree_div_apply h i j u hu]
    exact H u hu hx

theorem agree_nxt_apply {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (m : Fin n) (u : kˣ)
    (hu : valuation k (u : k) = 1) : nxt ψ m u = nxt ω m u := by
  unfold nxt
  split_ifs
  · exact h _ u hu
  · rfl

theorem agree_ev {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (m : Fin n) (x : k) :
    ev (ψ m / nxt ψ m) x = ev (ω m / nxt ω m) x := by
  unfold ev
  split_ifs with hx
  · have hv : valuation k ((Units.mk0 x fun h0 => by simp [h0] at hx : kˣ) : k) = 1 := by
      simpa using hx
    rw [MonoidHom.div_apply, MonoidHom.div_apply, h m _ hv, agree_nxt_apply h m _ hv]
  · rfl

theorem agree_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ ω : Fin n → kˣ →* ℂˣ), Agree ψ ω → grp ψ = grp ω ∧ theta ψ = theta ω ∧ (Ordered ψ → Ordered ω) ∧
      ∀ r, Cut ψ r → Cut ω r := by
  intro k _ _ _ _ n ψ ω h
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext g
    simp only [grp, Set.mem_setOf_eq, agree_triv_iff h]
  · funext g
    unfold theta
    exact Finset.prod_congr rfl fun m _ => agree_ev h m _
  · intro H i a b j hi ha hb x hT
    rw [← agree_triv_iff h]
    exact H i a b j hi ha hb x ((agree_triv_iff h i j x).2 hT)
  · intro r H i j hi hj hT
    exact H i j hi hj ((agree_triv_iff h i j 1).2 hT)

end GlobalTheory.PsType
end

section

open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.KummerEisensteinGalois

theorem map_smF_hom {K L : Type} [Field K] [CharZero K] [Field L] [CharZero L] (f : K →+* L) (c : ℤ) (j M : ℕ) (ζ : K)
    (a b : ℤ) (n : ℕ) : f (smF c j M ζ a b n) = smF c j M (f ζ) a b n := by
  simp [smF, eisF, const0, coefPos, apply_ite f, map_ofNat]

theorem map_cmul_hom {K L : Type} [Field K] [CharZero K] [Field L] [CharZero L] (f : K →+* L) (u v : ℕ → K) (n : ℕ) :
    f (cmul u v n) = cmul (fun i => f (u i)) (fun i => f (v i)) n := by

  simp [cmul, map_sum, map_mul]

theorem map_one_dirichlet {K L : Type} [Field K] [Field L] (f : K →+* L) (q : ℕ) (x : ZMod q) :
    f ((1 : DirichletCharacter K q) x) = (1 : DirichletCharacter L q) x := by
  by_cases h : IsUnit x
  · obtain ⟨u, rfl⟩ := h
    simp [MulChar.one_apply_coe]
  · simp [MulChar.map_nonunit _ h]

theorem map_pieceT_one : ∀ (N p m k : ℕ) [NeZero p] (K L : Type) [Field K] [CharZero K] [Field L] [CharZero L] (f : K →+* L) (c d : ℤ) (w w' : ℤ × ℤ)
    (ζ : K) (S : Finset (GL (Fin 2) (ZMod (p ^ m)))) (r : ℕ),
    f (pieceT N p m m k (1 : DirichletCharacter K (p ^ m)) c d w w' ζ S r) =
      pieceT N p m m k (1 : DirichletCharacter L (p ^ m)) c d w w' (f ζ) S r := by
  intro N p m k _ K L _ _ _ _ f c d w w' ζ S r

  simp only [pieceT, map_mul, map_neg, map_zpow₀, map_natCast, map_sum, map_cmul_hom, map_smF_hom, map_one_dirichlet]

end GlobalTheory.KummerEisensteinGalois
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

theorem dif_comp_add (L : ℕ) (ι : ℤ × ℤ → ℤ × ℤ) (hι : ∀ x v : ℤ × ℤ, ∀ r : ℤ, ι (x + r • v) = ι x + r • ι v)
    (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => F (ι y)) = fun x => dif L (ι v) F (ι x) := by
  funext x
  simp only [dif, hι]

theorem lat_dilate : ∀ (j L N : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ τ' : ℍ), 0 < N → (τ' : ℂ) = N * τ →
    lat j 0 L v Φ τ' = lat j 0 L ((N : ℤ) * v.1, v.2) (fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0) τ := by
  intro j L N v Φ τ τ' hN hτ
  set ι : ℤ × ℤ → ℤ × ℤ := fun x => ((N : ℤ) * x.1, x.2) with hιdef
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinj : Function.Injective ι := by
    intro a b h
    simp only [hιdef, Prod.mk.injEq] at h
    exact Prod.ext (mul_left_cancel₀ hN' h.1) h.2
  have hι : ∀ x v : ℤ × ℤ, ∀ r : ℤ, ι (x + r • v) = ι x + r • ι v := by
    intro x v r
    simp only [hιdef, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.mk_add_mk,
      Prod.smul_mk]
    ext <;> simp only <;> ring
  set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT
  have hG : (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) = fun y => T (ι y) := by
    funext y
    simp only [hT, hιdef, hτ]
    congr 1
    push_cast
    ring
  have hvι : ι v = ((N : ℤ) * v.1, v.2) := rfl
  have hdd : ∀ x, dif L v (dif L v fun y => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) x =
      dif L (ι v) (dif L (ι v) T) (ι x) := by
    intro x
    rw [hG, dif_comp_add L ι hι, dif_comp_add L ι hι]
  set Ψ : ℤ × ℤ → ℂ := fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0 with hΨ
  have hΨι : ∀ x, Ψ (ι x) = Φ x := by
    intro x
    simp only [hΨ, hιdef, dvd_mul_right, if_true, Int.mul_ediv_cancel_left _ hN']
  unfold lat
  rw [← hvι]
  simp_rw [hdd]
  set D := dif L (ι v) (dif L (ι v) T) with hD
  have key : (fun x => Φ x * D (ι x)) = fun x => (fun y => Ψ y * D y) (ι x) := by
    funext x; simp only [hΨι]
  rw [key]
  refine hinj.tsum_eq (f := fun y => Ψ y * D y) ?_
  intro y hy
  simp only [Function.mem_support] at hy
  by_cases h : (N : ℤ) ∣ y.1
  · obtain ⟨c, hc⟩ := h
    exact ⟨(c, y.2), by simp only [hιdef]; exact Prod.ext hc.symm rfl⟩
  · exact absurd (by simp only [hΨ, h, if_false, zero_mul]) hy

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory

theorem latF_rows_subst : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (φ : ZMod l → ℂ) (a b c d : ℤ),
    (N : ℤ) * a * d - l * b * c = 1 → 0 < N → 0 < l → ∀ y : ℤ × ℤ,
    (if (N : ℤ) ∣ y.1 then latF l (ch ν) φ (y.1 / N * (N * d) - y.2 * (l * c), -(y.1 / N * b) + y.2 * a) else 0) =
      latF (N * l) (fun _ => 1) (fun z => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) y := by
  intro N l ν φ a b c d hdet hN hl y
  obtain ⟨y1, y2⟩ := y
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcop : IsCoprime ((N : ℤ) * d) (l : ℤ) := ⟨a, -(b * c), by linear_combination hdet⟩
  simp only [latF]
  by_cases h1 : (N : ℤ) ∣ y1
  · obtain ⟨m, rfl⟩ := h1
    rw [if_pos (dvd_mul_right _ _)]
    have hdiv : (N : ℤ) * m / N = m := Int.mul_ediv_cancel_left m hNz
    simp only [hdiv]
    have key : ((N : ℤ) * l ∣ N * m) ↔ ((l : ℤ) ∣ m) := by
      constructor
      · intro h; exact (mul_dvd_mul_iff_left hNz).mp h
      · intro h; exact mul_dvd_mul_left _ h
    have key2 : ((l : ℤ) ∣ m * (N * d) - y2 * (l * c)) ↔ ((l : ℤ) ∣ m) := by
      constructor
      · intro h
        have h' : (l : ℤ) ∣ m * (N * d) := by
          have := dvd_add h (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)
          simpa using this
        exact hcop.symm.dvd_of_dvd_mul_right h'
      · intro h
        exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)
    push_cast
    by_cases h2 : (l : ℤ) ∣ m
    · obtain ⟨m2, rfl⟩ := h2
      rw [if_pos ((key2).mpr (dvd_mul_right _ _)), if_pos (key.mpr (dvd_mul_right _ _))]
      have hlz : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
      have e1 : (l : ℤ) * m2 * (N * d) - y2 * (l * c) = l * (m2 * N * d - y2 * c) := by ring
      rw [e1, Int.mul_ediv_cancel_left _ hlz]
      simp only [ch, one_mul, map_intCast]
      congr 2
      · push_cast
        simp [mul_comm]
      · push_cast
        simp [mul_comm]
    · rw [if_neg (fun h => h2 (key2.mp h)), if_neg (fun h => h2 (key.mp h))]
  · rw [if_neg h1, if_neg]
    intro h
    push_cast at h
    exact h1 (dvd_trans (dvd_mul_right _ _) h)

end GlobalTheory
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.CyclotomicQExpansion

theorem qD_sub (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (a b d : ℚ) (hk : 0 < a / d)
    (φ : HahnSeries ℚ Ω) :
    qD (sub ε a b d φ) = HahnSeries.C (algebraMap ℚ Ω (a / d)) * sub ε a b d (qD φ) := by
  have hcm : ∀ (c : ℚ → Ω) (ψ : HahnSeries ℚ Ω) (r : ℚ), (cm c ψ).coeff r = c r * ψ.coeff r :=
    fun _ _ _ => rfl
  have hsc : ∀ (ψ : HahnSeries ℚ Ω) (r : ℚ), (scale (a / d) ψ).coeff (a / d * r) = ψ.coeff r := by
    intro ψ r
    rw [scale, dite_eq_left hk]
    exact HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (a / d) hk).toOrderEmbedding) (a := r)
  rw [HahnSeries.C_mul_eq_smul]
  ext s
  obtain ⟨r, rfl⟩ : ∃ r, s = a / d * r := ⟨s / (a / d), (mul_div_cancel₀ s hk.ne').symm⟩
  rw [HahnSeries.coeff_smul]
  simp only [qD, sub]
  rw [hcm, hsc, hsc, hcm, hcm, hcm, smul_eq_mul, map_mul]
  ring

end GlobalTheory.CyclotomicQExpansion
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.finite_galois_approximation : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Gal p Ω → Finset Ω, ∃ F : Finset (Gal p Ω), ∀ h : Gal p Ω, ∃ g ∈ F, ∀ x ∈ S g, h x = g x := by
  first | exact @GlobalTheory.K5.gal_finite_subcover | exact GlobalTheory.K5.gal_finite_subcover | (intros; apply GlobalTheory.K5.gal_finite_subcover <;> assumption)
end
