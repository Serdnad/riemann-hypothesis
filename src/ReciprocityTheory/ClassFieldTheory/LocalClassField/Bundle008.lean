module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle007
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GroupCohomology.Bundle004
import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot
public import ReciprocityTheory.GroupCohomology.Bundle002

@[expose] public section

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions

open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

noncomputable def sigO (σ : GK p K) : Obar p →+* Obar p :=
  ((σ : PadicAlgCl p →+* PadicAlgCl p).comp (Obar p).subtype).codRestrict (Obar p)
    (fun x => mem_Obar_iff.2 (by
      change ‖σ (x : PadicAlgCl p)‖ ≤ 1
      rw [norm_GK]; exact norm_le_one x))

theorem coe_sigO (σ : GK p K) (x : Obar p) : ((sigO σ x : Obar p) : PadicAlgCl p) = σ x := rfl

noncomputable def sigBar (σ : GK p K) : kbar p →+* kbar p :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (Obar p)) (res.comp (sigO σ)) (by
    intro a ha
    have h1 : res a = 0 := (IsLocalRing.residue_eq_zero_iff a).2 ha
    rw [res_eq_zero_iff] at h1
    change res (sigO σ a) = 0
    rw [res_eq_zero_iff, coe_sigO, norm_GK]
    exact h1)

theorem sigBar_res (σ : GK p K) (x : Obar p) : sigBar σ (res x) = res (sigO σ x) := rfl

theorem sigBar_red (σ : GK p K) {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) : sigBar σ (red x) = red (σ x) := by
  rw [red_of_le hx, sigBar_res, ← red_coe, coe_sigO]

theorem sigBar_of_mem (σ : GK p K) {c : kbar p} (hc : c ∈ resK p K) : sigBar σ c = c := by
  obtain ⟨x, hx, rfl⟩ := (mem_resK_iff K c).1 hc
  rw [sigBar_res]
  congr 1
  apply Subtype.ext
  rw [coe_sigO]
  exact σ.commutes ⟨x, hx⟩

theorem pow_pow_succ_sub {R : Type*} [Monoid R] {q n : ℕ} (hq : 0 < q) {c : R} (h : c ^ (q ^ n - 1) = 1) :
    c ^ (q ^ n) = c := by
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ hq
  have : q ^ n = (q ^ n - 1) + 1 := by omega
  rw [this, pow_succ, h, one_mul]

theorem exists_pow_of_GK (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (σ : GK p K)
    {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K ^ n - 1) = 1) : ∃ i < n, σ ζ = ζ ^ (qK p K ^ i) := by
  obtain ⟨f, hf, hqf⟩ := qK_eq_pow K hK
  have hq := one_lt_qK K hK
  set q := qK p K with hqdef
  have hnd : ¬ p ∣ q ^ n - 1 := not_dvd_qK_pow_sub_one K hK hn
  have hm0 : q ^ n - 1 ≠ 0 := by rintro h; exact hnd (h ▸ dvd_zero p)
  have h1 := norm_eq_one_of_pow hm0 hζ
  set c := red ζ with hc
  have hcn : c ^ (q ^ n) = c := by
    rw [hc, ← red_pow h1.le, pow_pow_succ_sub (by omega) hζ]
  have : ExpChar (kbar p) p := ExpChar.prime Fact.out
  let φ : kbar p →+* kbar p := iterateFrobenius (kbar p) p f
  have hφ : ∀ x, φ x = x ^ q := fun x => by rw [hqf]; rfl
  let g : ℕ → (kbar p)[X] := fun i => X - C (c ^ (q ^ i))
  set h : (kbar p)[X] := ∏ i ∈ Finset.range n, g i with hh
  have hg : ∀ i, (g i).map φ = g (i + 1) := by
    intro i
    simp only [g, Polynomial.map_sub, map_X, map_C, hφ]
    rw [← pow_mul, ← pow_succ]
  have hmap : h.map φ = h := by
    rw [hh, Polynomial.map_prod]
    simp only [hg]
    have e1 := Finset.prod_range_succ g n
    have e2 := Finset.prod_range_succ' g n
    have e3 : g n = g 0 := by simp only [g, hcn, pow_zero, pow_one]
    have e4 : g 0 ≠ 0 := X_sub_C_ne_zero _
    rw [e1, e3] at e2
    exact (mul_right_cancel₀ e4 e2).symm
  have hcoef : ∀ k, h.coeff k ∈ resK p K := by
    intro k
    apply mem_resK_of_pow K hK
    rw [← hφ, ← coeff_map, hmap]
  have hmapσ : h.map (sigBar σ) = h := by
    ext k
    rw [coeff_map, sigBar_of_mem σ (hcoef k)]
  have h0 : h.eval c = 0 := by
    rw [hh, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.2 hn)
    simp [g]
  have h2 : h.eval (sigBar σ c) = 0 := by
    conv_lhs => rw [← hmapσ]
    rw [eval_map, eval₂_at_apply, h0, map_zero]
  rw [hh, eval_prod, Finset.prod_eq_zero_iff] at h2
  obtain ⟨i, hi, h3⟩ := h2
  refine ⟨i, Finset.mem_range.1 hi, ?_⟩
  simp only [g, eval_sub, eval_X, eval_C, sub_eq_zero] at h3
  rw [hc, sigBar_red σ h1.le, ← red_pow h1.le] at h3
  by_contra hne
  have hσζ : (σ ζ) ^ (q ^ n - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hζi : (ζ ^ (q ^ i)) ^ (q ^ n - 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have h4 := norm_sub_eq_one_of_pow_eq_one hnd hσζ hζi hne
  have h5 := (red_eq_iff (norm_eq_one_of_pow hm0 hσζ).le (norm_eq_one_of_pow hm0 hζi).le).1 h3
  exact absurd h4 (ne_of_lt h5)

variable (K)

theorem le_Kn (n : ℕ) : K ≤ Kn p K n := le_sup_left

theorem mem_Kn_of_pow {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K ^ n - 1) = 1) : ζ ∈ Kn p K n :=
  (le_sup_right : _ ≤ Kn p K n) (IntermediateField.subset_adjoin _ _ hζ)

theorem Kn_le {n : ℕ} {S : IntermediateField ℚ_[p] (PadicAlgCl p)} (h1 : K ≤ S)
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → ζ ∈ S) : Kn p K n ≤ S :=
  sup_le h1 (IntermediateField.adjoin_le_iff.2 h2)

theorem map_mem_Kn (n : ℕ) (σ : GK p K) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n := by
  have h : Kn p K n ≤ (Kn p K n).comap ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
      PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) := by
    apply Kn_le
    · intro y hy
      change σ y ∈ Kn p K n
      have : σ y = y := σ.commutes ⟨y, hy⟩
      rw [this]; exact le_Kn K n hy
    · intro ζ hζ
      change σ ζ ∈ Kn p K n
      apply mem_Kn_of_pow
      rw [← map_pow, hζ, map_one]
  exact h hx

noncomputable def eqField (σ τ : GK p K) : IntermediateField ℚ_[p] (PadicAlgCl p) where
  toSubalgebra := AlgHom.equalizer
    ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p)
    ((τ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p)
  inv_mem' := by
    intro x hx
    have hx' : σ x = τ x := hx
    change σ x⁻¹ = τ x⁻¹
    rw [map_inv₀, map_inv₀, hx']

theorem eqOn_Kn {n : ℕ} {σ τ : GK p K}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → σ ζ = τ ζ) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) :
    σ x = τ x := by
  have h1 : Kn p K n ≤ eqField K σ τ := by
    apply Kn_le
    · intro y hy
      change σ y = τ y
      exact (σ.commutes ⟨y, hy⟩).trans (τ.commutes ⟨y, hy⟩).symm
    · exact h
  exact h1 hx

theorem Kn_mono {m n : ℕ} (h : m ∣ n) : Kn p K m ≤ Kn p K n := by
  apply Kn_le K (le_Kn K n)
  intro ζ hζ
  apply mem_Kn_of_pow
  obtain ⟨k, rfl⟩ := h
  obtain ⟨d, hd⟩ : qK p K ^ m - 1 ∣ qK p K ^ (m * k) - 1 := by
    rw [pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow (qK p K ^ m) 1 k
  rw [hd, pow_mul, hζ, one_pow]

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem hom_f_injective {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (hφ : Surjective P.φ) (hu : Injective P.u) (n : ℕ) :
    Injective (P.hom.f n) := by
  intro t t' h
  refine Subtype.ext (funext fun v => ?_)
  choose v' hv' using fun i => hφ (v i)
  have := congrFun (congrArg Subtype.val h) v'
  have h2 : P.u (t.1 fun i => P.φ (v' i)) = P.u (t'.1 fun i => P.φ (v' i)) := this
  have h3 : (fun i => P.φ (v' i)) = v := funext hv'
  rw [h3] at h2
  exact hu h2

variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)

theorem cur_inf (hP : IsInvRep M N Q P) (z : Q.coch.X 2) (g h : G) :
    cur M (P.hom.f 2 z) g h = P.u (cur Q z (g : G ⧸ N) (h : G ⧸ N)) := by
  have hφa : ∀ a, P.φ a = (a : G ⧸ N) := fun a => by rw [hP.1]; rfl
  show P.u (z.1 _) = P.u (z.1 _)
  refine congrArg (fun v => P.u (z.1 v)) (funext fun i => ?_)
  fin_cases i
  · exact hφa g
  · exact hφa h

theorem phi_surjective (hP : IsInvRep M N Q P) : Surjective P.φ := by
  rw [hP.1]; exact QuotientGroup.mk'_surjective N

theorem descend2 (hN : IsOpen (N : Set G)) (hP : IsInvRep M N Q P) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0)
    (h0 : ∀ n ∈ N, ∀ g, cur M x n g = 0 ∧ cur M x g n = 0) :
    ∃ z : Q.coch.X 2, Q.coch.d 2 z = 0 ∧ P.hom.f 2 z = x := by
  have : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hN
  have hC := fun n hn g h => stepC (ρ := M.rho) (N := N) (c := cur M x)
    (isTwoCocycle_curried M x hx)
    (fun n hn g => (h0 n hn g).1) (fun n hn g => (h0 n hn g).2)
    n hn g h
  have hmem : ∀ g h, ∃ q, P.u q = cur M x g h := fun g h => (hP.2.2 _).2 fun n hn => (hC n hn g h).2.2
  choose F0 hF0 using hmem
  let z : Q.coch.X 2 := ⟨fun v => F0 (v 0).out (v 1).out, continuous_of_discreteTopology⟩
  have hz : P.hom.f 2 z = x := by
    refine ext2 M fun g h => ?_
    rw [cur_inf M N Q P hP]
    show P.u (F0 (g : G ⧸ N).out (h : G ⧸ N).out) = _
    obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul N g
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul N h
    rw [hF0, ha, hb, (hC _ a.2 _ _).2.1, (hC _ b.2 _ _).1]
  refine ⟨z, ?_, hz⟩
  apply hom_f_injective P (phi_surjective M N Q P hP) hP.2.1.injective 3
  rw [P.hom.comm, hz, hx, map_zero]

theorem exact2 (hN : IsOpen (N : Set G)) (hP : IsInvRep M N Q P) (h1 : Subsingleton ((M.resSub N).H 1)) :
    Exact (P.hom.H 2) ((Pair.res M N.subtype continuous_subtype_val).hom.H 2) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [H_mk, mk_eq_zero_iff] at hy
    have hx := (memZ _).1 x.2
    obtain ⟨w, hw⟩ := norm_all M N hN h1 x.1 hx hy
    obtain ⟨z, hz, hzx⟩ := descend2 M N Q P hN hP _ (d_sub_d M x.1 hx w) hw
    refine ⟨Submodule.Quotient.mk ⟨z, (memZ _).2 hz⟩, ?_⟩
    rw [H_mk, Submodule.Quotient.eq, Submodule.mem_comap]
    show P.hom.f 2 z - x.1 ∈ M.coch.B 2
    rw [hzx, memB]
    exact ⟨-w, by rw [map_neg]; abel⟩
  · rintro ⟨y0, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y0
    rw [H_mk, H_mk, mk_eq_zero_iff, memB]
    have hinv : ∀ n ∈ N, M.rho n (P.u (cur Q z.1 1 1)) = P.u (cur Q z.1 1 1) := (hP.2.2 _).1 ⟨_, rfl⟩
    refine ⟨mk1 (M.resSub N) (fun _ => P.u (cur Q z.1 1 1)) continuous_const, ?_⟩
    refine ext2 (M.resSub N) fun a b => ?_
    refine (curried_coboundary_eq (M.resSub N) _ continuous_const a b).trans ?_
    have e : cur (M.resSub N) ((Pair.res M N.subtype continuous_subtype_val).hom.Z 2 (P.hom.Z 2 z)).1 a b =
        cur M (P.hom.f 2 z.1) a b := by
      refine congrArg (P.hom.f 2 z.1).1 (funext fun i => ?_)
      fin_cases i <;> rfl
    rw [e, cur_inf M N Q P hP, (QuotientGroup.eq_one_iff _).2 a.2, (QuotientGroup.eq_one_iff _).2 b.2]
    simp only [D1]
    have := hinv a a.2
    have h' : (M.resSub N).rho a (P.u (cur Q z.1 1 1)) = P.u (cur Q z.1 1 1) := this
    rw [h']; abel

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem one_lt_p_real : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

variable {p K} in
theorem coe_units_ne_zero (x : Kˣ) : ((x : K) : PadicAlgCl p) ≠ 0 := fun h => x.ne_zero (Subtype.ext h)

variable {p K} in
theorem norm_units_pos (x : Kˣ) : 0 < ‖((x : K) : PadicAlgCl p)‖ := norm_pos_iff.2 (coe_units_ne_zero x)

theorem vK_spec (x : Kˣ) : (vK p K x : ℝ) = - (eK p K * Real.logb p ‖((x : K) : PadicAlgCl p)‖) := by
  unfold vK
  rw [vOn_spec, vbar_apply]
  show (eK p K : ℝ) * - Real.logb p ‖((x : K) : PadicAlgCl p)‖ = _
  ring

theorem vK_one : vK p K 1 = 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [vK_spec]; simp

theorem vK_mul (x y : Kˣ) : vK p K (x * y) = vK p K x + vK p K y := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_add, vK_spec, vK_spec, vK_spec, Units.val_mul, MulMemClass.coe_mul, norm_mul,
    Real.logb_mul (norm_units_pos x).ne' (norm_units_pos y).ne']
  ring

def vKHom : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (vK p K x)
  map_one' := by rw [vK_one]; rfl
  map_mul' x y := by rw [vK_mul]; rfl

theorem vKHom_apply (x : Kˣ) : vKHom p K x = Multiplicative.ofAdd (vK p K x) := rfl

theorem vK_inv (x : Kˣ) : vK p K x⁻¹ = - vK p K x := by
  have h := vK_mul p K x⁻¹ x
  rw [inv_mul_cancel, vK_one] at h
  omega

theorem vK_zpow (x : Kˣ) (n : ℤ) : vK p K (x ^ n) = n * vK p K x := by
  have h := map_zpow (vKHom p K) x n
  rw [vKHom_apply, vKHom_apply, ← ofAdd_zsmul] at h
  simpa using Multiplicative.ofAdd.injective h

theorem vK_pow (x : Kˣ) (n : ℕ) : vK p K (x ^ n) = n * vK p K x := by
  have h := vK_zpow p K x n
  rwa [zpow_natCast] at h

variable {p} in
theorem norm_algHom {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : E →ₐ[ℚ_[p]] PadicAlgCl p) (x : E) :
    ‖σ x‖ = ‖(x : PadicAlgCl p)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq E.val E.val.injective]
  rfl

variable {K L}

theorem finDim_of_le (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) : FiniteDimensional ℚ_[p] K :=
  FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap (IntermediateField.inclusion h).injective

theorem finDim_extendScalars_of_le (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    FiniteDimensional K (IntermediateField.extendScalars h) := by
  have : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars h) := hL
  exact FiniteDimensional.right ℚ_[p] K _

theorem norm_algebraNorm (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : IntermediateField.extendScalars h) :
    ‖((Algebra.norm K x : K) : PadicAlgCl p)‖ =
      ‖(x : PadicAlgCl p)‖ ^ Module.finrank K (IntermediateField.extendScalars h) := by
  have := finDim_extendScalars_of_le p hL h
  have h1 := Algebra.norm_eq_prod_embeddings K (PadicAlgCl p) x
  have h2 : ((Algebra.norm K x : K) : PadicAlgCl p) = algebraMap K (PadicAlgCl p) (Algebra.norm K x) := rfl
  rw [h2, h1, norm_prod, Finset.prod_congr rfl (fun σ _ => ?_), Finset.prod_const, Finset.card_univ,
    AlgHom.card]
  exact norm_algHom (E := L) (σ.restrictScalars ℚ_[p]) ⟨x.1, x.2⟩

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem kbarT_rho_ofK (g : GK p K) (a : Additive Kˣ) : (kbarT p K).rho g (ofK p K a) = ofK p K a :=
  Units.ext (g.commutes _)

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_int_of_mk_eq {x y : ℚ} (h : (QuotientAddGroup.mk x : QZ) = QuotientAddGroup.mk y) :
    ∃ n : ℤ, (n : ℚ) = x - y := by
  have h0 : (QuotientAddGroup.mk (x - y) : QZ) = 0 := by
    rw [QuotientAddGroup.mk_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (QuotientAddGroup.eq_zero_iff _).1 h0
  exact ⟨n, hn⟩

theorem exists_defect (χ : Additive G →+ QZ) (t : G → ℚ)
    (ht : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ (Additive.ofMul g)) :
    ∃ m : (Fin 2 → G) → ℤ, ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
  have h : ∀ g : Fin 2 → G, ∃ n : ℤ, (n : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := fun g =>
    exists_int_of_mk_eq (by rw [QuotientAddGroup.mk_add, ht, ht, ht, ofMul_mul, map_add (f := _)])
  choose m hm using h
  exact ⟨m, hm⟩

theorem defect_isLocallyConstant {t : G → ℚ} (ht : IsLocallyConstant t) {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) : IsLocallyConstant m := by
  have h : IsLocallyConstant (fun g : Fin 2 → G => t (g 0) + t (g 1) - t (g 0 * g 1)) :=
    ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
      (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))
  refine IsLocallyConstant.desc m (fun n : ℤ => (n : ℚ)) ?_ Int.cast_injective
  have e : (fun n : ℤ => (n : ℚ)) ∘ m = fun g : Fin 2 → G => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
  rw [e]; exact h

theorem defect_cocycle {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (v : Fin 3 → G) :
    m ![v 1, v 2] - m ![v 0 * v 1, v 2] + m ![v 0, v 1 * v 2] - m ![v 0, v 1] = 0 := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, hm, hm, hm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]
  ring

theorem trep_dn_one {R : Type} [CommRing R] (M : TRep R G) (f : (Fin 1 → G) → M.V) (v : Fin 2 → G) :
    ReciprocityTheory.Gal.dn M.rho 1 f v = M.rho (v 0) (f ![v 1]) - f ![v 0 * v 1] + f ![v 0] :=
  LowDeg.dn_one_apply M.rho f v

theorem trep_dn_two {R : Type} [CommRing R] (M : TRep R G) (f : (Fin 2 → G) → M.V) (v : Fin 3 → G) :
    ReciprocityTheory.Gal.dn M.rho 2 f v = M.rho (v 0) (f ![v 1, v 2]) - f ![v 0 * v 1, v 2] + f ![v 0, v 1 * v 2] -
      f ![v 0, v 1] :=
  LowDeg.dn_two_apply M.rho f v

variable (M : TRep ℤ G)

theorem exists_defect_cocycle {a : M.V} (ha : ∀ g, M.rho g a = a) {t : G → ℚ} (ht : IsLocallyConstant t)
    {m : (Fin 2 → G) → ℤ} (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) :
    ∃ (z : M.coch.X 2) (_ : M.coch.d 2 z = 0), ∀ g, z.1 g = m g • a := by
  refine ⟨⟨fun g => m g • a, ((defect_isLocallyConstant ht hm).comp (· • a)).continuous⟩, ?_, fun g => rfl⟩
  refine LowDeg.coch_d_eq_zero M (funext fun v => ?_)
  rw [trep_dn_two]
  show M.rho (v 0) (m ![v 1, v 2] • a) - m ![v 0 * v 1, v 2] • a + m ![v 0, v 1 * v 2] • a - m ![v 0, v 1] • a = 0
  rw [map_zsmul, ha, ← sub_smul, ← add_smul, ← sub_smul, defect_cocycle hm, zero_smul]

theorem defect_cls_eq {a : M.V} (ha : ∀ g, M.rho g a = a) {t t' : G → ℚ} (ht : IsLocallyConstant t)
    (ht' : IsLocallyConstant t') (htt : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = QuotientAddGroup.mk (t' g))
    {m m' : (Fin 2 → G) → ℤ} (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1))
    (hm' : ∀ g, (m' g : ℚ) = t' (g 0) + t' (g 1) - t' (g 0 * g 1))
    {z z' : M.coch.X 2} (hz : M.coch.d 2 z = 0) (hz' : M.coch.d 2 z' = 0)
    (hzv : ∀ g, z.1 g = m g • a) (hzv' : ∀ g, z'.1 g = m' g • a) :
    M.coch.cls 2 z hz = M.coch.cls 2 z' hz' := by
  choose u hu using fun g => exists_int_of_mk_eq (htt g)
  have hul : IsLocallyConstant u := by
    refine IsLocallyConstant.desc u (fun n : ℤ => (n : ℚ)) ?_ Int.cast_injective
    have e : (fun n : ℤ => (n : ℚ)) ∘ u = fun g => t g - t' g := funext hu
    rw [e]; exact ht.sub ht'
  rw [Cx.cls_eq_iff]
  refine ⟨⟨fun g => u (g 0) • a,
    ((hul.comp_continuous (continuous_apply 0)).comp (· • a)).continuous⟩, Subtype.ext (funext fun v => ?_)⟩
  refine (trep_dn_one M (fun g => u (g 0) • a) v).trans ?_
  show M.rho (v 0) (u (v 1) • a) - u (v 0 * v 1) • a + u (v 0) • a = z.1 v - z'.1 v
  rw [hzv, hzv']
  rw [map_zsmul, ha, ← sub_smul, ← add_smul, ← sub_smul]
  congr 1
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hu, hu, hu, hm, hm']
  ring

end General

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
