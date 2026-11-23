module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem quot_equiv (K : Type) [Field K] (m : ℕ) :
    Nonempty ((PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) ≃ (Fin m → K)) := by
  let f : PowerSeries K →+ (Fin m → K) :=
    { toFun := fun p i => PowerSeries.coeff (i : ℕ) p
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hs : Function.Surjective f := by
    intro v
    refine ⟨PowerSeries.mk fun i => if h : i < m then v ⟨i, h⟩ else 0, ?_⟩
    ext i
    simp [f]
  have hk : (Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}).toAddSubgroup = f.ker := by
    ext p
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff, AddMonoidHom.mem_ker]
    constructor
    · intro h; ext i; exact h i i.2
    · intro h i hi; exact congrFun h ⟨i, hi⟩
  exact ⟨((QuotientAddGroup.quotientAddEquivOfEq hk).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hs)).toEquiv⟩

private theorem l_zero (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] (φ : ℤ_[l] →+* K) : (l : K) = 0 := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite K p
  have hpp : p.Prime := (CharP.char_is_prime_or_zero K p).resolve_right hp0
  by_cases hpl : p = l
  · subst hpl
    exact CharP.cast_eq_zero K p
  · exfalso
    have hu : IsUnit (p : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) ?_
      have h1 : ¬ ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
        rw [PadicInt.norm_int_lt_one_iff_dvd]
        intro hd
        have e := (Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hpp).1 (Int.natCast_dvd_natCast.1 hd)
        exact hpl e.symm
      push_neg at h1
      simpa using h1
    have hu' := hu.map φ
    rw [map_natCast, CharP.cast_eq_zero K p] at hu'
    exact not_isUnit_zero hu'

theorem UpperTheory.V.Pa.am_fin :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (m g : ℕ), Finite (x.Am m) ∧ Nat.card (x.Am m) = Nat.card x.K ^ m ∧ IsNilpotent (algebraMap x.A (x.Am m) x.t) ∧ IsNilpotent (algebraMap x.A (DD (x.Am m) g) x.t) ∧ (l : x.A) = 0 ∧ 1 < Nat.card x.K := by
  intro l _ F n x m g
  obtain ⟨e⟩ := quot_equiv x.K m
  have hn : IsNilpotent (algebraMap x.A (x.Am m) x.t) := ⟨m, by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩
  refine ⟨Finite.of_equiv _ e.symm, ?_, hn, hn.map (DD.C : x.Am m →+* DD (x.Am m) g), ?_, Finite.one_lt_card⟩
  · rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]
  · have h := l_zero l x.K (algebraMap ℤ_[l] x.K)
    rw [← map_natCast (PowerSeries.C (R := x.K)), h, map_zero]
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem adic_lin {G R : Type} [TopologicalSpace G] [CommRing R] (I : Ideal R) (c : R) {f f' : G → R}
    (h : AdicCont I f) (h' : AdicCont I f') : AdicCont I fun g => c * f g + f' g := by
  intro N
  have e : (fun g => (Ideal.Quotient.mk (I ^ N)) (c * f g + f' g)) =
      fun g => Ideal.Quotient.mk (I ^ N) c * Ideal.Quotient.mk (I ^ N) (f g) + Ideal.Quotient.mk (I ^ N) (f' g) := by
    funext g
    simp only [map_add (f := _), map_mul]
  rw [e]
  exact ((IsLocallyConstant.const _).mul (h N)).add (h' N)

private theorem adic_zero {G R : Type} [TopologicalSpace G] [CommRing R] (I : Ideal R) :
    AdicCont I fun _ : G => (0 : R) := fun _ => IsLocallyConstant.const _

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
  (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)

private theorem dY_lin (c : A) (Y Y' : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (c • Y + Y') g = c • dY F ρ Y g + dY F ρ Y' g := by
  simp only [dY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  abel

private theorem dY_zero (g : F.G₀) : dY F ρ 0 g = 0 := by simp [dY]

private theorem locAt_lin (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (c : A) {z z' : F.G₀ → Matrix (Fin n) (Fin n) R}
    {v : F.Vl} {Y Y' : Matrix (Fin n) (Fin n) R} (h : LocAt F ρ w wi z v Y) (h' : LocAt F ρ w wi z' v Y') :
    LocAt F ρ w wi (c • z + z') v (c • Y + Y') := by
  intro g
  obtain ⟨h1, h2⟩ := h g
  obtain ⟨h1', h2'⟩ := h' g
  have key : wi v * ((c • z + z') ((F.φ v) g) - dY F ρ (c • Y + Y') ((F.φ v) g)) * w v =
      c • (wi v * (z ((F.φ v) g) - dY F ρ Y ((F.φ v) g)) * w v) +
        wi v * (z' ((F.φ v) g) - dY F ρ Y' ((F.φ v) g)) * w v := by
    rw [dY_lin]
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
  · rw [key, Matrix.add_apply, Matrix.smul_apply, h1 i j hij, h1' i j hij, smul_zero, add_zero]
  · rw [key, Matrix.add_apply, Matrix.smul_apply, h2 hg i, h2' hg i, smul_zero, add_zero]

end

private theorem sub_of_lin {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (s : Set M) (h0 : (0 : M) ∈ s)
    (h : ∀ (c : A) x y, x ∈ s → y ∈ s → c • x + y ∈ s) : ∃ S : Submodule A M, (S : Set M) = s := by
  refine ⟨{ carrier := s, add_mem' := ?_, zero_mem' := h0, smul_mem' := ?_ }, rfl⟩
  · intro x y hx hy
    have := h 1 x y hx hy
    rwa [one_smul] at this
  · intro c x hx
    have := h c x 0 hx h0
    rwa [add_zero] at this

theorem UpperTheory.V.Pa.sel_lin :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), (∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = SelZ F t ρ w wi V) ∧ ∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = Bd F ρ V := by
  intro l _ F n A R _ _ _ t ρ w wi V
  constructor
  · apply sub_of_lin
    · refine ⟨fun _ => V.zero_mem, fun i j => ?_, fun g h => by simp, fun g => by simp, fun u g _ => rfl,
        fun v => ⟨0, V.zero_mem, fun g => ?_⟩⟩
      · exact adic_zero _
      · simp [dY_zero]
    · intro c x y hx hy
      obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hx
      obtain ⟨y1, y2, y3, y4, y5, y6⟩ := hy
      refine ⟨fun g => V.add_mem (V.smul_mem c (x1 g)) (y1 g), fun i j => ?_, fun g h => ?_, fun g => ?_,
        fun u g hg => ?_, fun v => ?_⟩
      · have e : (fun g => (c • x + y) g i j) = fun g => algebraMap A R c * x g i j + y g i j := by
          funext g
          rw [Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, Algebra.smul_def]
        rw [e]
        exact adic_lin _ _ (x2 i j) (y2 i j)
      · simp only [Pi.add_apply, Pi.smul_apply, x3 g h, y3 g h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul, smul_add]
        abel
      · simp only [Pi.add_apply, Pi.smul_apply, x4 g, y4 g, Matrix.transpose_add, Matrix.transpose_smul,
          Matrix.transpose_neg, smul_neg]
        abel
      · simp [x5 u g hg, y5 u g hg]
      · obtain ⟨Y, hY, hYl⟩ := x6 v
        obtain ⟨Y', hY', hYl'⟩ := y6 v
        exact ⟨c • Y + Y', V.add_mem (V.smul_mem c hY) hY', locAt_lin F ρ w wi c hYl hYl'⟩
  · apply sub_of_lin
    · exact ⟨0, V.zero_mem, by simp, funext fun g => (dY_zero F ρ g).symm⟩
    · rintro c x y ⟨Y, hY, hYt, rfl⟩ ⟨Y', hY', hYt', rfl⟩
      refine ⟨c • Y + Y', V.add_mem (V.smul_mem c hY) hY', ?_, ?_⟩
      · rw [Matrix.transpose_add, Matrix.transpose_smul, hYt, hYt', smul_neg, neg_add]
      · funext g
        rw [dY_lin]
        rfl
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pl_sub :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (H K : Subgroup Γ) [H.Normal] [K.Normal], IsOpen (K : Set Γ) → H ≤ K → ∀ U : OpenNormalSubgroup K, (∀ h : K, (h : Γ) ∈ H → ∃ e : ℕ, h ^ l ^ e ∈ U) → ∀ g : K, (g : Γ) ∈ PL (l := l) H → g ∈ U := by
  intro l _ Γ _ _ _ _ _ H K _ _ hK hHK U hU g hg
  have hl : l.Prime := Fact.out
  have hKc : IsClosed (K : Set Γ) := OpenSubgroup.isClosed ⟨K, hK⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc.isCompact
  haveI : U.toSubgroup.FiniteIndex := U.toOpenSubgroup.toSubgroup.finiteIndex_of_finite_quotient
  haveI : U.toSubgroup.Normal := U.isNormal'
  have hn0 : U.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have lem : ∀ k : K, (k : Γ) ∈ H → k ^ l ^ U.toSubgroup.index ∈ U.toSubgroup := by
    intro k hk
    obtain ⟨e, he⟩ := hU k hk
    set q : K ⧸ U.toSubgroup := (QuotientGroup.mk k : K ⧸ U.toSubgroup)
    have hqe : q ^ l ^ e = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact he
    have hqn : q ^ U.toSubgroup.index = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact U.toSubgroup.pow_index_mem k
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hqe)
    have h1 : l ^ a ≤ U.toSubgroup.index := by
      rw [← ha]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (orderOf_dvd_of_pow_eq_one hqn)
    have h2 : a < l ^ a := Nat.lt_pow_self hl.one_lt
    have h3 : orderOf q ∣ l ^ U.toSubgroup.index := by
      rw [ha]
      exact pow_dvd_pow l (by omega)
    have hq : q ^ l ^ U.toSubgroup.index = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hq
    exact hq
  let O : Subgroup Γ := U.toSubgroup.map K.subtype
  have hOo : IsOpen (O : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hK.isOpenMap_subtype_val _ U.toOpenSubgroup.isOpen
  have hOc : IsClosed (O : Set Γ) := OpenSubgroup.isClosed ⟨O, hOo⟩
  haveI : Finite (Γ ⧸ O) := O.quotient_finite_of_isOpen hOo
  haveI : O.FiniteIndex := O.finiteIndex_of_finite_quotient
  have hCo : IsOpen (O.normalCore : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (O.normalCore_isClosed hOc)
  let C : OpenNormalSubgroup Γ :=
    { toOpenSubgroup := ⟨O.normalCore, hCo⟩
      isNormal' := O.normalCore_normal }
  have hcond : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ C.toOpenSubgroup := by
    intro h hh
    refine ⟨U.toSubgroup.index, ?_⟩
    show ∀ b : Γ, b * h ^ l ^ U.toSubgroup.index * b⁻¹ ∈ O
    intro b
    rw [← conj_pow]
    have hbH : b * h * b⁻¹ ∈ H := ‹H.Normal›.conj_mem h hh b
    have hm := lem ⟨b * h * b⁻¹, hHK hbH⟩ hbH
    exact Subgroup.mem_map.mpr ⟨_, hm, rfl⟩
  have hgC : (g : Γ) ∈ C.toOpenSubgroup := by
    unfold PL at hg
    exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hg C) hcond
  have hgO : (g : Γ) ∈ O := O.normalCore_le hgC
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgO
  have : x = g := Subtype.ext hxg
  rw [← this]
  exact hx
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.hom_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (A A' B B' : Glob l L) (a : A.Hom A') (b : B.Hom B') (h : A.Hom B), a.p.ker ≤ (b.p.comp h.p).ker → ∃ h' : A'.Hom B', ∀ x, h'.p (a.p x) = b.p (h.p x) := by
  intro l _ L A A' B B' a b h hk
  have hT1 : T1Space A'.Γ := by
    refine ⟨fun x => ?_⟩
    have h1 : IsPreconnected (closure ({x} : Set A'.Γ)) := isPreconnected_singleton.closure
    have h2 := h1.subsingleton
    have h3 : closure ({x} : Set A'.Γ) = {x} :=
      h2.eq_singleton_of_mem (subset_closure (Set.mem_singleton x))
    exact closure_eq_iff_isClosed.mp h3
  have hT2 : T2Space A'.Γ := inferInstance
  let q : A'.Γ →* B'.Γ := a.p.liftOfRightInverse (Function.surjInv a.surj)
    (Function.rightInverse_surjInv a.surj) ⟨b.p.comp h.p, hk⟩
  have hq : ∀ x, q (a.p x) = b.p (h.p x) := fun x =>
    a.p.liftOfRightInverse_comp_apply _ _ ⟨b.p.comp h.p, hk⟩ x
  have hquot : Topology.IsQuotientMap a.p :=
    a.cont.isClosedMap.isQuotientMap a.cont a.surj
  refine ⟨⟨q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hq⟩
  · rw [hquot.continuous_iff]
    have : (q : A'.Γ → B'.Γ) ∘ a.p = fun x => b.p (h.p x) := funext hq
    rw [this]
    exact b.cont.comp h.cont
  · intro y
    obtain ⟨z, rfl⟩ := b.surj y
    obtain ⟨x, rfl⟩ := h.surj z
    exact ⟨a.p x, hq x⟩
  · intro g
    obtain ⟨x, rfl⟩ := a.surj g
    rw [hq, b.η, h.η, a.η]
  · rw [← a.c, hq, h.c, b.c]
  · intro g
    obtain ⟨x, rfl⟩ := a.surj g
    rw [hq, b.ε, h.ε, a.ε]
  · intro v g
    rw [← a.φ, hq, h.φ, b.φ]
  · intro v g
    rw [← a.φu, hq, h.φu, b.φu]
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section

variable {A R R' : Type} [CommRing A] [CommRing R] [Algebra A R] [CommRing R'] [Algebra A R'] (f : R →ₐ[A] R') {n : ℕ}

private theorem adic_map {G : Type} [TopologicalSpace G] (t : A) (u : G → R)
    (hu : AdicCont (Ideal.span {algebraMap A R t}) u) :
    AdicCont (Ideal.span {algebraMap A R' t}) fun g => f (u g) := by
  intro N
  have hmap : Ideal.map f ((Ideal.span {algebraMap A R t}) ^ N) =
      (Ideal.span {algebraMap A R' t}) ^ N := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, AlgHom.commutes]
  have hle : (Ideal.span {algebraMap A R t}) ^ N ≤
      ((Ideal.span {algebraMap A R' t}) ^ N).comap (f : R →+* R') := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hmap.le
  have e : (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R' t}) ^ N) (f (u g))) =
      (Ideal.quotientMap _ (f : R →+* R') hle) ∘
        (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R t}) ^ N) (u g)) := by
    funext g
    simp [Ideal.quotientMap_mk]
  change IsLocallyConstant (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R' t}) ^ N) (f (u g)))
  rw [e]
  exact (hu N).comp _

private theorem mm_mul (M N : Matrix (Fin n) (Fin n) R) : (M * N).map f = M.map f * N.map f :=
  map_mul f.mapMatrix M N

private theorem mm_add (M N : Matrix (Fin n) (Fin n) R) : (M + N).map f = M.map f + N.map f :=
  map_add f.mapMatrix M N

private theorem mm_sub (M N : Matrix (Fin n) (Fin n) R) : (M - N).map f = M.map f - N.map f :=
  map_sub f.mapMatrix M N

private theorem mm_neg (M : Matrix (Fin n) (Fin n) R) : (-M).map f = -M.map f :=
  map_neg f.mapMatrix M

private theorem dY_map {l : ℕ} [Fact l.Prime] (F : GFrame l) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)
    (Y : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    (dY F ρ Y g).map f = dY F (fun g => (ρ g).map f) (Y.map f) g := by
  unfold dY
  rw [mm_sub, mm_mul, mm_mul]

end

theorem UpperTheory.V.Pa.sel_map :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (A R R' : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R'] [Algebra A R'] (f : R →ₐ[A] R') (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) (V' : Submodule A (Matrix (Fin n) (Fin n) R')), (∀ Z ∈ V, Z.map f ∈ V') → ∀ z, (z ∈ SelZ F t ρ w wi V → (fun g => (z g).map f) ∈ SelZ F t (fun g => (ρ g).map f) (fun v => (w v).map f) (fun v => (wi v).map f) V') ∧ (z ∈ Bd F ρ V → (fun g => (z g).map f) ∈ Bd F (fun g => (ρ g).map f) V') := by
  intro l _ F n A R R' _ _ _ _ _ f t ρ w wi V V' hV z
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => hV _ (h1 g), fun i j => ?_, fun g k => ?_, fun g => ?_, fun u g hg => ?_,
      fun v => ?_⟩
    · exact adic_map f t (fun g => z g i j) (h2 i j)
    · beta_reduce
      rw [h3, mm_add, mm_mul, mm_mul]
    · beta_reduce
      rw [h4, mm_neg, Matrix.transpose_map]
    · beta_reduce
      rw [h5 u g hg]
      exact Matrix.map_zero _ (map_zero f)
    · obtain ⟨Y, hY, hloc⟩ := h6 v
      refine ⟨Y.map f, hV _ hY, fun g => ?_⟩
      have key : (wi v).map f * ((z ((F.φ v) g)).map f -
            dY F (fun g => (ρ g).map f) (Y.map f) ((F.φ v) g)) * (w v).map f =
          (wi v * (z ((F.φ v) g) - dY F ρ Y ((F.φ v) g)) * w v).map f := by
        rw [mm_mul, mm_mul, mm_sub, dY_map]
      obtain ⟨hl1, hl2⟩ := hloc g
      refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
      · beta_reduce
        rw [key, Matrix.map_apply, hl1 i j hij, map_zero]
      · beta_reduce
        rw [key, Matrix.map_apply, hl2 hg i, map_zero]
  · rintro ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map f, hV _ hY, ?_, ?_⟩
    · rw [← Matrix.transpose_map, hT, mm_neg]
    · funext g
      exact dY_map f F ρ Y g
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pl_map :
    ∀ (l : ℕ) [Fact l.Prime] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (f : Γ →* Γ') (H : Subgroup Γ') [H.Normal],
      IsOpen (H : Set Γ') → Continuous f → Function.Surjective f →
        (PL (l := l) (H.comap f)).map f = PL (l := l) H := by
  intro l _ Γ Γ' _ _ _ _ _ _ _ _ _ _ f H _ _ hf hsurj
  have hmem {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {x : G} :
      x ∈ PL (l := l) K ↔
        ∀ U : OpenNormalSubgroup G, (∀ h ∈ K, ∃ e : ℕ, h ^ l ^ e ∈ U) → x ∈ U := by
    simp only [PL, Subgroup.mem_iInf]
    rfl
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine hmem.mpr fun V hV => ?_
    let U : OpenNormalSubgroup Γ :=
      { toOpenSubgroup := V.toOpenSubgroup.comap f hf
        isNormal' := Subgroup.Normal.comap V.isNormal' f }
    apply hmem.mp hx U
    intro h hh
    obtain ⟨e, he⟩ := hV (f h) hh
    refine ⟨e, ?_⟩
    change f (h ^ l ^ e) ∈ V
    rwa [map_pow]
  · intro y hy
    let ι := {U : OpenNormalSubgroup Γ // ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ U}
    let top : OpenNormalSubgroup Γ :=
      { toOpenSubgroup := ⊤
        isNormal' := Subgroup.normal_top }
    have htop : ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ top := by
      intro h _
      exact ⟨0, Subgroup.mem_top _⟩
    have : Nonempty ι := ⟨⟨top, htop⟩⟩
    let t (i : ι) : Set Γ := f ⁻¹' {y} ∩ (i.1 : Set Γ)
    have hclosed (i : ι) : IsClosed (t i) :=
      (isClosed_singleton.preimage hf).inter i.1.toOpenSubgroup.isClosed
    have hdir : Directed (· ⊇ ·) t := by
      intro i j
      have hpow : ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ i.1 ⊓ j.1 := by
        intro h hh
        obtain ⟨a, ha⟩ := i.2 h hh
        obtain ⟨b, hb⟩ := j.2 h hh
        refine ⟨a + b, ⟨?_, ?_⟩⟩
        · rw [pow_add, pow_mul]
          exact pow_mem ha _
        · rw [add_comm, pow_add, pow_mul]
          exact pow_mem hb _
      exact ⟨⟨i.1 ⊓ j.1, hpow⟩, fun _ hx => ⟨hx.1, hx.2.1⟩, fun _ hx => ⟨hx.1, hx.2.2⟩⟩
    have hnonempty (i : ι) : (t i).Nonempty := by
      let V : OpenNormalSubgroup Γ' :=
        { toSubgroup := i.1.toSubgroup.map f
          isOpen' := f.isOpenMap_of_sigmaCompact hsurj hf _ i.1.toOpenSubgroup.isOpen
          isNormal' := Subgroup.Normal.map i.1.isNormal' f hsurj }
      have hyV : y ∈ V := by
        refine hmem.mp hy V fun h hh => ?_
        obtain ⟨x, rfl⟩ := hsurj h
        obtain ⟨e, he⟩ := i.2 x hh
        exact ⟨e, ⟨x ^ l ^ e, he, map_pow f x _⟩⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hyV
      exact ⟨x, hxy, hx⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir
      hnonempty (fun i => (hclosed i).isCompact) hclosed
    rw [Set.mem_iInter] at hx
    exact ⟨x, hmem.mpr fun U hU => (hx ⟨U, hU⟩).2, (hx ⟨top, htop⟩).1⟩
end
