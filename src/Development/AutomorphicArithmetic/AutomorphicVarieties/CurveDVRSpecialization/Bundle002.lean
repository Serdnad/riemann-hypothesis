module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleCoverForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.HalesJewett
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.RingTheory.Filtration
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.LinearAlgebra.Vandermonde
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Polynomial

private theorem charPerm_dvd {G k : Type} [Group G] [Field k] (f : (G →* k) →₀ ℤ)
    (h : ∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f = 0) (ψ : G →* k) : ((ringChar k : ℕ) : ℤ) ∣ f ψ := by
  classical
  have hli := linearIndependent_monoidHom G k
  rw [linearIndependent_iff'] at hli
  have hsum : ∑ φ ∈ f.support, ((f φ : ℤ) : k) • ((φ : G →* k) : G → k) = 0 := by
    funext g
    have h0 := congrArg (fun u : k →₀ ℤ => u.sum (fun v z => (z : k) * v)) (h g)
    simp only [Finsupp.sum_zero_index] at h0
    rw [Finsupp.sum_mapDomain_index (by intro; simp) (by intro _ _ _; push_cast; ring)] at h0
    simpa [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h0
  by_cases hψ : ψ ∈ f.support
  · have := hli f.support (fun φ => ((f φ : ℤ) : k)) hsum ψ hψ
    exact (CharP.intCast_eq_zero_iff k (ringChar k) _).mp this
  · have : f ψ = 0 := by simpa using hψ
    rw [this]
    exact dvd_zero _

private theorem charPerm_zero {G k : Type} [Group G] [Field k] (f : (G →* k) →₀ ℤ)
    (h : ∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f = 0) : f = 0 := by
  classical
  by_cases hp : ringChar k = 0
  · ext ψ
    have := charPerm_dvd f h ψ
    rw [hp] at this
    simpa using this
  · have hp1 : 1 < ringChar k :=
      ((CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hp).one_lt
    have key : ∀ n : ℕ, ∀ f : (G →* k) →₀ ℤ, (∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f = 0) →
        ∀ ψ, ((ringChar k : ℕ) : ℤ) ^ n ∣ f ψ := by
      intro n
      induction n with
      | zero => intro f _ ψ; simp
      | succ n ih =>
        intro f hf ψ
        let f1 : (G →* k) →₀ ℤ := Finsupp.mapRange (fun z : ℤ => z / ((ringChar k : ℕ) : ℤ)) (by simp) f
        have hf1 : f = ((ringChar k : ℕ) : ℤ) • f1 := by
          ext φ
          simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, f1]
          exact (Int.mul_ediv_cancel' (charPerm_dvd f hf φ)).symm
        have hf1' : ∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f1 = 0 := by
          intro g
          have := hf g
          rw [hf1, Finsupp.mapDomain_smul] at this
          exact (smul_eq_zero.mp this).resolve_left (by exact_mod_cast hp)
        have := ih f1 hf1' ψ
        rw [hf1, Finsupp.smul_apply, smul_eq_mul, pow_succ']
        exact mul_dvd_mul_left _ this
    ext ψ
    have hd := key (f ψ).natAbs f h ψ
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
    simpa [Int.natAbs_pow] using Nat.lt_pow_self (n := (f ψ).natAbs) hp1

private theorem charPerm_single {α ι : Type} [Fintype ι] (a b : ι → α) :
    Finset.univ.val.map a = Finset.univ.val.map b ↔
      (∑ i, Finsupp.single (a i) (1 : ℤ)) = ∑ i, Finsupp.single (b i) (1 : ℤ) := by
  classical
  have key : ∀ (s : Multiset α) (x : α),
      (s.map (fun y => Finsupp.single y (1 : ℤ))).sum x = (s.count x : ℤ) := by
    intro s x
    induction s using Multiset.induction_on with
    | empty => simp
    | cons y s ih =>
      by_cases hxy : y = x
      · subst hxy
        simp [Multiset.count_cons, ih]
        try ring
      · simp [Multiset.count_cons, ih, Finsupp.single_apply, hxy, Ne.symm hxy]
  have hsum : ∀ c : ι → α, (∑ i, Finsupp.single (c i) (1 : ℤ)) =
      ((Finset.univ.val.map c).map (fun y => Finsupp.single y (1 : ℤ))).sum := by
    intro c
    rw [Finset.sum_eq_multiset_sum, Multiset.map_map]
    rfl
  constructor
  · intro h
    rw [hsum, hsum, h]
  · intro h
    refine Multiset.ext.mpr fun x => ?_
    have := DFunLike.congr_fun h x
    rw [hsum, hsum, key, key] at this
    exact_mod_cast this

private theorem charPerm_perm {α ι : Type} [Fintype ι] (a b : ι → α)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) : ∃ σ : Equiv.Perm ι, ∀ i, b i = a (σ i) := by
  classical
  have hc : ∀ c, Fintype.card {i // b i = c} = Fintype.card {i // a i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    simp only [Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_def, Finset.card_def,
      Finset.filter_val, Finset.filter_val]
    have e : ∀ d : ι → α, Multiset.filter (fun x => d x = c) Finset.univ.val =
        Multiset.filter (fun x => c = d x) Finset.univ.val :=
      fun d => Multiset.filter_congr (fun x _ => eq_comm)
    rw [e, e]
    convert this.symm
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), fun i => ?_⟩
  exact (Equiv.ofFiberEquiv_map _ i).symm

theorem UpperTheory.V.Pr.charPerm :
    UpperTheory.V.Pr.CharPerm := by
  intro G k _ _ n χ χ' hχ
  classical
  let ψ : Fin n → (G →* k) := fun i => (Units.coeHom k).comp (χ i)
  let ψ' : Fin n → (G →* k) := fun i => (Units.coeHom k).comp (χ' i)
  have hr : ∀ a : Fin n → k, (∏ i, (X - C (a i))).roots = Finset.univ.val.map a := by
    intro a
    rw [Finset.prod_eq_multiset_prod]
    have : Finset.univ.val.map (fun i => X - C (a i)) = (Finset.univ.val.map a).map (fun x => X - C x) := by
      rw [Multiset.map_map]
      rfl
    rw [this, Polynomial.roots_multiset_prod_X_sub_C]
  have hroots : ∀ g, Finset.univ.val.map (fun i => ψ i g) = Finset.univ.val.map (fun i => ψ' i g) := by
    intro g
    have h1 := congrArg Polynomial.roots (hχ g)
    unfold UpperTheory.V.Pr.chPoly at h1
    rw [hr, hr] at h1
    exact h1
  let f : (G →* k) →₀ ℤ := (∑ i, Finsupp.single (ψ' i) (1 : ℤ)) - ∑ i, Finsupp.single (ψ i) 1
  have hf : ∀ g, Finsupp.mapDomain (fun φ : G →* k => φ g) f = 0 := by
    intro g
    simp only [f, Finsupp.mapDomain_sub, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
    rw [sub_eq_zero]
    exact (charPerm_single (fun i => ψ' i g) (fun i => ψ i g)).mp (hroots g).symm
  have hs : (∑ i, Finsupp.single (ψ i) (1 : ℤ)) = ∑ i, Finsupp.single (ψ' i) 1 :=
    (sub_eq_zero.mp (charPerm_zero f hf)).symm
  obtain ⟨σ, hσ⟩ := charPerm_perm ψ ψ' ((charPerm_single ψ ψ').mpr hs)
  refine ⟨σ, fun i => MonoidHom.ext fun g => Units.ext ?_⟩
  exact congrArg (fun φ : G →* k => φ g) (hσ i)
end

section


open IsLocalRing Filter Topology in
theorem UpperTheory.V.Pr.linClosedOfAdic :
    UpperTheory.V.Pr.LinClosedOfAdic := by
  intro G A κ _ _ _ _ _ _ j hj n a ha f
  classical
  let e : (Fin n × Fin n → A) → Matrix (Fin n) (Fin n) κ :=
    fun y => Matrix.of fun s t => j (y (s, t))
  let K : Submodule A (Fin n × Fin n → A) :=
    { carrier := {y | f (e y) = 0}
      add_mem' := by
        intro x y hx hy
        have h : e (x + y) = e x + e y := by
          ext s t
          simp [e]
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [h, map_add (f := _), hx, hy, add_zero]
      zero_mem' := by
        have h : e 0 = 0 := by
          ext s t
          simp [e]
        simp only [Set.mem_setOf_eq]
        rw [h, map_zero]
      smul_mem' := by
        intro r x hx
        have h : e (r • x) = j r • e x := by
          ext s t
          simp [e]
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [h, map_smul, hx, smul_zero] }
  let y : G → (Fin n × Fin n → A) := fun g p => a g p.1 p.2
  have hy : ∀ g, (a g).map j = e (y g) := fun g => by
    ext s t
    simp [e, y]
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro g0 hg0
  have hK : K.mkQ (y g0) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    intro h
    apply hg0
    show f ((a g0).map j) = 0
    rw [hy]
    exact h
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := A)
    (M := (Fin n × Fin n → A) ⧸ K) (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
  obtain ⟨N, hN⟩ : ∃ N : ℕ, K.mkQ (y g0) ∉
      (maximalIdeal A ^ N • ⊤ : Submodule A ((Fin n × Fin n → A) ⧸ K)) := by
    by_contra h
    push_neg at h
    apply hK
    have hm : K.mkQ (y g0) ∈
        (⨅ i : ℕ, maximalIdeal A ^ i • ⊤ : Submodule A ((Fin n × Fin n → A) ⧸ K)) :=
      Submodule.mem_iInf _ |>.mpr h
    rw [hbot] at hm
    exact (Submodule.mem_bot A).mp hm
  let U : Set G := ⋂ p : Fin n × Fin n, {g | Ideal.Quotient.mk (maximalIdeal A ^ N) (a g p.1 p.2) =
    Ideal.Quotient.mk (maximalIdeal A ^ N) (a g0 p.1 p.2)}
  refine ⟨U, ?_, ?_, ?_⟩
  · intro g hg hgS
    apply hN
    have hd : ∀ p, y g p - y g0 p ∈ maximalIdeal A ^ N := by
      intro p
      have hp := Set.mem_iInter.mp hg p
      simp only [Set.mem_setOf_eq] at hp
      rw [← Ideal.Quotient.eq]
      exact hp
    have h0 : K.mkQ (y g) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      show f (e (y g)) = 0
      rw [← hy]
      exact hgS
    have hsum : y g - y g0 = ∑ p, (y g p - y g0 p) • Pi.single p (1 : A) := by
      funext q
      rw [Finset.sum_apply]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hmem : K.mkQ (y g - y g0) ∈
        (maximalIdeal A ^ N • ⊤ : Submodule A ((Fin n × Fin n → A) ⧸ K)) := by

      rw [hsum, map_sum]
      refine Submodule.sum_mem _ fun p _ => ?_
      rw [LinearMap.map_smul]
      exact Submodule.smul_mem_smul (hd p) Submodule.mem_top
    rw [map_sub, h0, zero_sub] at hmem
    exact neg_mem_iff.mp hmem
  · apply isOpen_iInter_of_finite
    intro p
    exact (ha p.1 p.2 N).isOpen_fiber _
  · exact Set.mem_iInter.mpr fun p => rfl
end

section

open Matrix

theorem UpperTheory.V.Pr.strongIrrOfOpen :
    UpperTheory.V.Pr.StrongIrrOfOpen := by
  intro G κ _ _ _ _ n r hlin hirr W S hS hiff
  have hset : (S : Set G) = ⋂ v ∈ W, ⋂ φ ∈ W.dualAnnihilator,
      {g | φ (UpperTheory.V.Pr.gm r g *ᵥ v) = 0} := by
    ext g
    simp only [SetLike.mem_coe, hiff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h v hv φ hφ
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mpr (h v hv) φ hφ
    · intro h v hv
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp (h v hv)
  have hclosed : IsClosed (S : Set G) := by
    rw [hset]
    refine isClosed_biInter fun v _ => isClosed_biInter fun φ _ => ?_
    let f : Matrix (Fin n) (Fin n) κ →ₗ[κ] κ :=
      { toFun := fun M => φ (M *ᵥ v)
        map_add' := by
          intro A B
          simp [Matrix.add_mulVec]
        map_smul' := by
          intro c A
          simp [Matrix.smul_mulVec] }
    exact hlin f
  have hopen : IsOpen (S : Set G) := S.isOpen_of_isClosed_of_finiteIndex hclosed
  apply hirr S hopen W
  intro g hg v hv
  exact (hiff g).mp hg v hv
end

section

namespace UpperTheory.V.Pr

open IsLocalRing

theorem constOfAlg : ConstOfAlg := by
  intro k A _ _ _ _ _ x c hx hm
  by_contra hne
  have hy : x - algebraMap k A c ≠ 0 := sub_ne_zero.mpr hne
  have hint : IsIntegral k (x - algebraMap k A c) :=
    hx.isIntegral.sub isIntegral_algebraMap
  exact (maximalIdeal.isMaximal A).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hm (hint.isUnit hy))

end UpperTheory.V.Pr
end

section

open scoped Pointwise in
theorem UpperTheory.V.Pr.commonFree :
    UpperTheory.V.Pr.CommonFree := by
  intro H A ι _ _ _ χ N hN htor hex
  classical
  let K : ι → Subgroup H := fun i => ((powMonoidHom N : A →* A).comp (χ i)).ker
  have hK : ∀ i h, h ∈ K i ↔ χ i h ^ N = 1 := fun i h => by
    simp [K, MonoidHom.mem_ker]
  by_contra hno
  push_neg at hno
  have _ : Fintype ι := Fintype.ofFinite ι
  have hcov : ⋃ i ∈ (Finset.univ : Finset ι), (fun _ => (1 : H)) i • ((K i : Set H)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro h
    obtain ⟨i, m, hm, h1⟩ := hno h
    simp only [one_smul, Set.mem_iUnion, Finset.mem_univ, exists_true_left, SetLike.mem_coe, exists_const]
    exact ⟨i, (hK i h).2 (htor i h m hm h1)⟩
  obtain ⟨i, -, hfin⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcov
  obtain ⟨h, hh⟩ := hex i
  apply hh
  haveI : (K i).Normal := MonoidHom.normal_ker _
  have hmem := (K i).pow_index_mem h
  rw [hK, map_pow, ← pow_mul] at hmem
  exact htor i h _ (Nat.mul_pos (Nat.pos_of_ne_zero hfin.index_ne_zero) hN) hmem
end

section

theorem UpperTheory.V.Pr.expSums :
    UpperTheory.V.Pr.ExpSums := by
  intro κ ι σ _ _ _ α c hα hc
  classical
  by_contra hne
  push Not at hne
  choose C hC using hne
  obtain ⟨a, ha, b, s, hs⟩ :=
    Combinatorics.exists_mono_homothetic_copy (Finset.range (Fintype.card ι)) C
  let e := (Fintype.equivFin ι).symm
  have hinj : Function.Injective fun j : Fin (Fintype.card ι) => ((α s (e j) : κˣ) : κ) ^ a := by
    intro i j hij
    by_contra h
    refine hα s (e i) (e j) (fun h' => h (e.injective h')) a ha ?_
    apply Units.ext
    simpa using hij
  have h0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (v := fun j => c s (e j) * ((α s (e j) : κˣ) : κ) ^ b) hinj (by
      intro i
      have h1 := hC (a • (i : ℕ) + b)
      rw [hs i (Finset.mem_range.2 i.2), ← e.sum_comp] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, pow_add, pow_mul]
      ring)
  obtain ⟨i, hi⟩ := hc s
  have h2 := congrFun h0 (e.symm i)
  simp only [Equiv.apply_symm_apply, Pi.zero_apply, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact hi h2
  · exact pow_ne_zero _ (α s i).ne_zero h2
end

section

namespace UpperTheory.V.Pr

open Matrix

private theorem comb {G ι : Type} [Group G] [Fintype ι] (R : G → ι → ι → Prop)
    (h1 : ∀ i, R 1 i i) (hinv : ∀ g i, ∃ k, R g i k ∧ R g⁻¹ k i)
    (hc : ∀ g h, ∃ x, (∀ i k j, R g i k → R h k j → R x i j) ∧
      (∀ i k j, R h⁻¹ i k → R g⁻¹ k j → R x⁻¹ i j)) :
    ∃ b, (∀ i, R b i i) ∧ (∀ i j, R b i j → R b⁻¹ i j) ∧
      ∀ g i k l j, R g i k → R b k l → R g⁻¹ l j → R b i j := by
  classical
  let T : G → Finset (Bool × ι × ι) := fun g =>
    Finset.univ.filter fun s => if s.1 then R g s.2.1 s.2.2 else R g⁻¹ s.2.1 s.2.2
  let P : G → Prop := fun g => (∀ i, R g i i) ∧ ∀ i, R g⁻¹ i i
  have hP1 : P 1 := ⟨h1, by rw [inv_one]; exact h1⟩
  obtain ⟨b, hb, hmax⟩ : ∃ b, P b ∧ ∀ c, P c → (T c).card ≤ (T b).card := by
    have hfin : ((fun g => (T g).card) '' {g | P g}).Finite :=
      (Set.finite_Iic (Fintype.card (Bool × ι × ι))).subset (by
        rintro _ ⟨g, _, rfl⟩
        exact Finset.card_le_univ _)
    obtain ⟨_, ⟨b, hb, rfl⟩, hm⟩ := Set.exists_max_image _ id hfin ⟨_, 1, hP1, rfl⟩
    exact ⟨b, hb, fun c hc => hm _ ⟨c, hc, rfl⟩⟩
  have key : ∀ c, P c → (∀ i j, R c i j → R b i j) ∧ ∀ i j, R c⁻¹ i j → R b⁻¹ i j := by
    intro c hcP
    obtain ⟨x, hx1, hx2⟩ := hc b c
    have hPx : P x := ⟨fun i => hx1 i i i (hb.1 i) (hcP.1 i), fun i => hx2 i i i (hcP.2 i) (hb.2 i)⟩
    have hsub : T b ⊆ T x := by
      rintro ⟨t, i, j⟩ hs
      cases t
      · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_eq_true, if_false] at hs ⊢
        exact hx2 i i j (hcP.2 i) hs
      · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, if_true] at hs ⊢
        exact hx1 i j j hs (hcP.1 j)
    have heq : T b = T x := Finset.eq_of_subset_of_card_le hsub (hmax x hPx)
    constructor
    · intro i j hij
      have : ((true, i, j) : Bool × ι × ι) ∈ T x := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, if_true]
        exact hx1 i i j (hb.1 i) hij
      rw [← heq] at this
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and, if_true] using this
    · intro i j hij
      have : ((false, i, j) : Bool × ι × ι) ∈ T x := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_eq_true, if_false]
        exact hx2 i j j hij (hb.2 j)
      rw [← heq] at this
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_eq_true, if_false] using this
  refine ⟨b, hb.1, ?_, ?_⟩
  · have := (key b⁻¹ ⟨hb.2, by rw [inv_inv]; exact hb.1⟩).2
    rwa [inv_inv] at this
  · intro g i k l j hik hkl hlj
    obtain ⟨x, hx1, hx2⟩ := hc g b
    obtain ⟨y, hy1, hy2⟩ := hc x g⁻¹
    rw [inv_inv] at hy2
    have hPy : P y := by
      constructor
      · intro t
        obtain ⟨s, hs1, hs2⟩ := hinv g t
        exact hy1 t s t (hx1 t s s hs1 (hb.1 s)) hs2
      · intro t
        obtain ⟨s, hs1, hs2⟩ := hinv g t
        exact hy2 t s t hs1 (hx2 s s t (hb.2 s) hs2)
    exact (key y hPy).1 i j (hy1 i l j (hx1 i k l hik hkl) hlj)

end UpperTheory.V.Pr

open Matrix in
theorem UpperTheory.V.Pr.fullEx :
    UpperTheory.V.Pr.FullEx :=
  _root_.UpperTheory.Reformulated.B.StronglyIrreducibleFreeRatios.fullEx
end
