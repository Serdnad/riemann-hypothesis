module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
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
import Mathlib.RingTheory.TwoSidedIdeal.Instances
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
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem closed_zero {Γ K : Type} [TopologicalSpace Γ] [Field K] {f : Γ → PowerSeries K}
    (hf : AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) f) : IsClosed {g | f g = 0} := by
  have hset : {g | f g = 0} = ⋂ N : ℕ,
      {g | Ideal.Quotient.mk ((Ideal.span {(PowerSeries.X : PowerSeries K)}) ^ N) (f g) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · intro h N
      rw [h]
      exact dvd_zero _
    · intro h
      ext n
      have := (PowerSeries.X_pow_dvd_iff).1 (h (n + 1)) n (Nat.lt_succ_self n)
      simpa using this
  rw [hset]
  exact isClosed_iInter fun N => (hf N).isClosed_fiber 0

theorem UpperTheory.V.Pa.coc_ker :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (s : Set G.G₀) (z : G.G₀ → Matrix (Fin n) (Fin n) x.A), h.p.ker ≤ (Subgroup.normalClosure (Subtype.val '' s)).topologicalClosure → (∀ a ∈ s, h.p₀ a = 1 ∧ z a = 0) → z ∈ SelM h x x.A → ∃ y : G0.G₀ → Matrix (Fin n) (Fin n) x.A, ∀ g, y (h.p₀ g) = z g := by
  intro l _ L G G0 h n x s z hker hs hz
  obtain ⟨-, hcont, hcoc, hconj, -, -⟩ := hz
  have coc : ∀ g k : G.G₀,
      z (g * k) = z g + x.ρX x.A (h.p₀ g) * z k * x.ρX x.A (h.p₀ g⁻¹) := hcoc
  have hρ1 : ∀ g : G.G₀, h.p₀ g = 1 → x.ρX x.A (h.p₀ g) = 1 := by
    intro g hg
    rw [hg]
    simp [NP.ρX]
  have hz1 : z 1 = 0 := by
    have e := coc 1 1
    rw [hρ1 1 (map_one _), inv_one, hρ1 1 (map_one _), one_mul, mul_one] at e
    simpa using e
  have hR : ∀ g k : G.G₀, z k = 0 → z (g * k) = z g := by
    intro g k hk
    rw [coc, hk]
    simp
  let H : Subgroup G.G₀ :=
    { carrier := {k | h.p₀ k = 1 ∧ z k = 0}
      one_mem' := ⟨map_one _, hz1⟩
      mul_mem' := by
        rintro a b ⟨ha, za⟩ ⟨hb, zb⟩
        refine ⟨by rw [map_mul, ha, hb, one_mul], ?_⟩
        rw [hR a b zb, za]
      inv_mem' := by
        rintro a ⟨ha, za⟩
        refine ⟨by rw [map_inv, ha, inv_one], ?_⟩
        have e := hR a⁻¹ a za
        rw [inv_mul_cancel, hz1] at e
        exact e.symm }
  have hHconj : ∀ g k : G.G₀, k ∈ H → g * k * g⁻¹ ∈ H := by
    rintro g k ⟨hk1, hk2⟩
    refine ⟨by rw [map_mul, map_mul, hk1, mul_one, map_inv, mul_inv_cancel], ?_⟩
    have hkg : z (k * g⁻¹) = z g⁻¹ := by
      rw [coc, hk2, hρ1 k hk1]
      have : h.p₀ k⁻¹ = 1 := by rw [map_inv, hk1, inv_one]
      rw [hρ1 _ this]
      simp
    rw [mul_assoc, coc, hkg, ← coc, mul_inv_cancel, hz1]
  have hHc : ∀ k : G.G₀, k ∈ H → G.frame.conj k ∈ H := by
    rintro k ⟨hk1, hk2⟩
    refine ⟨?_, ?_⟩
    · rw [h.p₀_conj, hk1, map_one]
    · rw [hconj, hk2]
      simp
  let N : Subgroup G.Γ := H.map G.η.ker.subtype
  have hN : N.Normal := by
    constructor
    intro m hm γ
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hm
    rcases Int.units_eq_one_or (G.η γ) with hγ | hγ
    · have e : γ * (k : G.Γ) * γ⁻¹ = (((⟨γ, hγ⟩ : G.G₀) * k * (⟨γ, hγ⟩ : G.G₀)⁻¹ : G.G₀) : G.Γ) := rfl
      exact Subgroup.mem_map.2 ⟨_, hHconj _ _ hk, e.symm⟩
    · have hg : G.c⁻¹ * γ ∈ G.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, G.η_c, hγ]
        rfl
      let g : G.G₀ := ⟨G.c⁻¹ * γ, hg⟩
      have e : γ * (k : G.Γ) * γ⁻¹ = ((G.frame.conj (g * k * g⁻¹) : G.G₀) : G.Γ) := by
        show γ * (k : G.Γ) * γ⁻¹ = G.c * ((G.c⁻¹ * γ) * (k : G.Γ) * (G.c⁻¹ * γ)⁻¹) * G.c⁻¹
        group
      exact Subgroup.mem_map.2 ⟨_, hHc _ (hHconj _ _ hk), e.symm⟩
  have hHclosed : IsClosed (H : Set G.G₀) := by
    have e1 : (H : Set G.G₀) = {k | h.p₀ k = 1} ∩ ⋂ i, ⋂ j, {k | z k i j = 0} := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun i j => by rw [h2]; rfl⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Matrix.ext fun i j => h2 i j⟩
    rw [e1]
    exact IsClosed.inter ((isClosed_singleton (x := (1 : G0.G₀))).preimage h.p₀_cont)
      (isClosed_iInter fun i => isClosed_iInter fun j => closed_zero (hcont i j))
  have hNclosed : IsClosed (N : Set G.Γ) := by
    show IsClosed (Subtype.val '' (H : Set G.G₀))
    exact hHclosed.trans (Subgroup.isClosed_of_isOpen _ G.η_open)
  have hsN : Subtype.val '' s ⊆ (N : Set G.Γ) := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.2 ⟨a, ⟨(hs a ha).1, (hs a ha).2⟩, rfl⟩
  have hkerN : h.p.ker ≤ N :=
    hker.trans (Subgroup.topologicalClosure_minimal _
      (Subgroup.normalClosure_le_normal (N := N) hsN) hNclosed)
  have hfac : ∀ g g' : G.G₀, h.p₀ g = h.p₀ g' → z g = z g' := by
    intro g g' e
    have h1 : h.p₀ (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
    have h2 : ((g⁻¹ * g' : G.G₀) : G.Γ) ∈ h.p.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val h1
    obtain ⟨k, hk, hk'⟩ := Subgroup.mem_map.1 (hkerN h2)
    have hkk : k = g⁻¹ * g' := Subtype.ext hk'
    rw [hkk] at hk
    have e2 := hR g _ hk.2
    rw [mul_inv_cancel_left] at e2
    exact e2.symm
  exact ⟨fun g0 => z (Classical.choose (h.p₀_surj g0)),
    fun g => hfac _ _ (Classical.choose_spec (h.p₀_surj (h.p₀ g)))⟩
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_prime_power_pow_eq_one (l n N : ℕ) {B E : Type} [CommRing B] [Ring E] [Algebra B E] (m : Ideal B)
    (hN : ∀ a ∈ m ^ N, algebraMap B E a = 0) (hl : (l : B) ∈ m) (x : E) (p : Polynomial B)
    (hp : Polynomial.aeval x p = 0) (hc : ∀ i, (p - (Polynomial.X - 1) ^ n).coeff i ∈ m) :
    ∃ e : ℕ, x ^ l ^ e = 1 := by
  let K : Ideal (Polynomial B) := RingHom.ker (Polynomial.aeval x : Polynomial B →ₐ[B] E)
  have hm : m.map Polynomial.C ≤ K.radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    refine ⟨N, ?_⟩
    show Polynomial.aeval x (Polynomial.C a ^ N) = 0
    rw [← map_pow, Polynomial.aeval_C]
    exact hN _ (Ideal.pow_mem_pow ha N)
  have h1 : (Polynomial.X - 1 : Polynomial B) ∈ K.radical := by
    have h2 : p ∈ K.radical := Ideal.le_radical hp
    have h3 := K.radical.sub_mem h2 (hm (Ideal.mem_map_C_iff.2 hc))
    rw [sub_sub_cancel] at h3
    exact Ideal.mem_radical_of_pow_mem h3
  have h2 : (l : Polynomial B) ∈ K.radical := by
    have := hm (Ideal.mem_map_of_mem Polynomial.C hl)
    rwa [map_natCast] at this
  let J : Ideal (Polynomial B) := Ideal.span {(l : Polynomial B), Polynomial.X - 1}
  have hJ : J ≤ K.radical := by
    rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact h2
    · exact h1
  obtain ⟨j, hj⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ (Submodule.fg_span (Set.toFinite _))
  have h4 := pow_mem_of_sub_one_mem l (Polynomial B) J.toTwoSided
    (Ideal.mem_toTwoSided.2 (Ideal.subset_span (by simp))) j Polynomial.X
    (Ideal.mem_toTwoSided.2 (Ideal.subset_span (by simp)))
  rw [Ideal.asIdeal_toTwoSided] at h4
  have h5 : Polynomial.aeval x ((Polynomial.X : Polynomial B) ^ l ^ j - 1) = 0 :=
    hj (Ideal.pow_le_pow_right (Nat.le_succ j) h4)
  refine ⟨j, ?_⟩
  simpa [sub_eq_zero] using h5

private theorem ch_mem {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G) :
    Polynomial.aeval y (D.chi y) ∈ TwoSidedIdeal.span D.CH := by
  rw [← UpperTheory.V.CA.d_toDet_CH]
  have h1 := (UpperTheory.V.CA.d_chS D.toDet A).1 (1 ⊗ₜ y)
  have h2 : D.toDet.chiS A (1 ⊗ₜ y) = D.chi y := by
    show D.D _ (ofT A G _ _) = D.D _ _
    congr 1
    rw [map_sub, Algebra.TensorProduct.map_tmul, ofT_tmul, ofT_tmul, map_one, map_one, one_smul, MonoidAlgebra.one_def,
      MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rfl
  rw [h2] at h1
  have key : ∀ w ∈ Submodule.span A ((fun z : MonoidAlgebra A G => (1 : A) ⊗ₜ[A] z) '' (D.toDet.CH : Set (MonoidAlgebra A G))),
      Algebra.TensorProduct.lid A (MonoidAlgebra A G) w ∈ D.toDet.CH := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      simpa using hz
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul, Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  have h3 := key _ h1
  rw [← Polynomial.aeval_algHom_apply] at h3
  simpa using h3

private theorem chi_diag {n : ℕ} {k G : Type} [CommRing k] [Group G] (χ : Fin n → G →* kˣ) (g : G)
    (h : ∀ i, χ i g = 1) :
    (GDet.ofRep (diagRep χ)).chi (MonoidAlgebra.single g 1) = (Polynomial.X - 1) ^ n := by
  show (GDet.repAlg (diagRep χ) (Polynomial k) _).det = _
  have : GDet.repAlg (diagRep χ) (Polynomial k) (MonoidAlgebra.single 1 Polynomial.X -
      MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1)) =
      diagonal fun _ => Polynomial.X - 1 := by
    have e : diagRep χ g = 1 := by
      show diagonal (fun i => (χ i g : k)) = 1
      simp [h]
    ext1 a b
    by_cases hab : a = b <;> simp [GDet.repAlg, e, hab]
  rw [this, det_diagonal]
  simp

theorem UpperTheory.V.Pa.pl_chBar :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G : Glob l L) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a : G.G₀, (a : G.Γ) ∈ H → ∀ i, r.chib i a = 1) → ∀ (Z : Set (MonoidAlgebra B G.G₀)) (k : G.G₀), (k : G.Γ) ∈ PL l H → MonoidAlgebra.single k 1 - 1 ∈ u.D.chBar Z := by
  intro l _ L G n O _ _ _ hO _ r B _ _ _ u H _ _ hH hχ Z k hk
  simp only [GDet.chBar, closureIdeal, TwoSidedIdeal.mem_iInf]
  intro N V
  generalize hS : (u.D.CH ∪ Z ∪ _ ∪ _ : Set (MonoidAlgebra B G.G₀)) = S
  let I := TwoSidedIdeal.span S
  have hsub := hS.trans_subset (TwoSidedIdeal.subset_span (s := S))
  let q : MonoidAlgebra B G.G₀ →ₐ[B] I.ringCon.Quotient := RingCon.mkₐ B I.ringCon
  have hq : ∀ a b, q a = q b ↔ a - b ∈ I := fun a b =>
    (RingCon.eq _).trans (TwoSidedIdeal.rel_iff I a b)
  have hq0 : ∀ a ∈ I, q a = 0 := fun a ha => by
    rw [← map_zero q, hq, sub_zero]; exact ha
  let f : G.G₀ →* I.ringCon.Quotient := (q : _ →* _).comp (MonoidAlgebra.of B G.G₀)
  have hf : ∀ g, g ∈ f.ker ↔ MonoidAlgebra.single g 1 - 1 ∈ I := fun g => by
    rw [← hq, map_one]; rfl
  have hV : V.toSubgroup ≤ f.ker := fun g hg => (hf g).2 (hsub (Or.inr ⟨g, hg, rfl⟩))
  let U : OpenNormalSubgroup G.G₀ :=
    { toSubgroup := f.ker
      isOpen' := Subgroup.isOpen_mono hV V.isOpen
      isNormal' := MonoidHom.normal_ker f }
  refine (hf k).1 (pl_sub l G.Γ H G.η.ker G.η_open hH U (fun h hh => ?_) k hk)
  have hl : (l : B) ∈ maximalIdeal B := by
    have := hO.char
    rw [← res_eq_zero_iff O, map_natCast, CharP.cast_eq_zero]
  have hchi : (u.D.chi (MonoidAlgebra.single h 1)).map (res O B : B →+* ResidueField O) = (Polynomial.X - 1) ^ n := by
    rw [← ((UpperTheory.V.CA.d_gmap u.D).2.2.1 _ _).1, u.red, MonoidAlgebra.mapRingHom_single, map_one]
    exact chi_diag _ _ (hχ h hh)
  obtain ⟨e, he⟩ := exists_prime_power_pow_eq_one l n N (maximalIdeal B)
    (fun a ha => by
      rw [← q.commutes]
      exact hq0 _ (hsub (Or.inl (Or.inr ⟨a, ha, rfl⟩)))) hl (q (MonoidAlgebra.single h 1))
    (u.D.chi (MonoidAlgebra.single h 1))
    (by
      rw [Polynomial.aeval_algHom_apply]
      exact hq0 _ (TwoSidedIdeal.span_le.2 (fun z hz => hsub (Or.inl (Or.inl (Or.inl hz)))) (ch_mem u.D _)))
    (fun i => by
      rw [← res_eq_zero_iff O]
      show (res O B : B →+* ResidueField O) _ = 0
      rw [← Polynomial.coeff_map, Polynomial.map_sub, hchi]
      simp)
  refine ⟨e, ?_⟩
  show f (h ^ l ^ e) = 1
  rw [map_pow]
  exact he
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem chi_ofRep_single {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  · ext1 a b
    by_cases hab : a = b <;> simp [GDet.repAlg, hab, Matrix.one_apply, Matrix.diagonal_apply]
  · ext1 a b
    simp [GDet.repAlg]

private theorem kills_max {B K : Type} [CommRing B] [IsLocalRing B] [Field K] [Finite K] (g : B →+* K) (b : B)
    (hb : b ∈ maximalIdeal B) : g b = 0 := by
  by_contra h
  haveI := Fintype.ofFinite K
  have h1 := FiniteField.pow_card_sub_one_eq_one (g b) h
  have h2 : Fintype.card K - 1 ≠ 0 := by have := Fintype.one_lt_card (α := K); omega
  have h3 : IsUnit (1 - b ^ (Fintype.card K - 1)) :=
    isUnit_one_sub_self_of_mem_nonunits _ (Ideal.pow_mem_of_mem _ hb _ (Nat.pos_of_ne_zero h2))
  have h4 := h3.map g
  rw [map_sub, map_one, map_pow, h1, sub_self] at h4
  exact not_isUnit_zero h4

theorem UpperTheory.V.Pa.pt_unip :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (D0 : ℕ) (P : Pt T u D0), Adapted T (r := r) → P.x.UnipOn T.H.toSubgroup := by
  intro l _ L G0 T n O _ _ _ r B _ _ _ u D0 P hA
  refine UpperTheory.V.Pa.unip_of l G0.frame n P.x _ fun h hh => ?_
  have key : ∀ {C : Type} [CommRing C] (f : B →+* C), (u.D.map f).chi (MonoidAlgebra.single h 1) =
      (u.D.chi (MonoidAlgebra.single h 1)).map f := fun f => by
    have := ((UpperTheory.V.CA.d_gmap u.D).2.2.1 f (MonoidAlgebra.single h 1)).1
    rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
  have h1 := key P.f.toRingHom
  rw [P.maps.1, chi_ofRep_single] at h1
  have h2 := key (res O B : B →+* ResidueField O)
  rw [u.red, Resid.Dbar, chi_ofRep_single] at h2
  have h3 : (UpperTheory.V.W.diagRep r.chib) h = 1 := by
    change Matrix.diagonal (fun i => ((r.chib i h : (ResidueField O)ˣ) : ResidueField O)) = 1
    simp [hA.1 h hh]
  rw [h3, Matrix.charpoly_one, Fintype.card_fin] at h2
  have h4 : (u.D.chi (MonoidAlgebra.single h 1) - (Polynomial.X - 1) ^ n).map (res O B : B →+* ResidueField O) = 0 := by
    rw [Polynomial.map_sub, ← h2]
    simp
  have h5 : (u.D.chi (MonoidAlgebra.single h 1) - (Polynomial.X - 1) ^ n).map
      ((PowerSeries.constantCoeff : P.x.A →+* P.x.K).comp P.f.toRingHom) = 0 := by
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    refine kills_max _ _ ((res_eq_zero_iff O B _).1 ?_)
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) h4
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, RingHom.coe_coe] using this
  rw [Polynomial.map_sub, sub_eq_zero] at h5
  rw [h1, Polynomial.map_map, h5]
  simp
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem np_desc_sep {K : Type} [Field K] (a : PowerSeries K)
    (h : ∀ m : ℕ, a ∈ (Ideal.span {(PowerSeries.X : PowerSeries K)}) ^ m) : a = 0 := by
  ext i
  have := h (i + 1)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at this
  simpa using this i (Nat.lt_succ_self i)

theorem UpperTheory.V.Pa.np_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (x : NP G.frame n) (k : Kap x) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → x.UnipOn H → g.p.ker = PL l H → (∃ ρ' : G'.G₀ →* GL (Fin n) x.A, ∀ a, ρ' (g.p₀ a) = x.ρ a) ∧ ∃ κ' : Fin k.g → G'.G₀ → Matrix (Fin n) (Fin n) x.A, ∀ j a, κ' j (g.p₀ a) = k.κ j a := by
  intro l _ L G G' g n x k H _ hH hη hU hker
  have hρ : ∀ d, x.ρX x.A d = mat x.ρ d := by
    intro d
    ext i j
    simp [NP.ρX]
  obtain ⟨hR, -, -, -⟩ := rho_hom l G.frame n x k x.A
  have hl : (l : x.A) = 0 := by
    have := (am_fin l G.frame n x 0 0).2.2.2.2.1
    simpa using this
  have hunip : ∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e, ∀ i j,
      (x.ρX x.A (h ^ l ^ e) - 1) i j ∈ (Ideal.span {algebraMap x.A x.A x.t}) ^ m := by
    intro m h hh
    obtain ⟨e, he⟩ := hU m h hh
    refine ⟨e, fun i j => ?_⟩
    rw [hρ, show algebraMap x.A x.A x.t = x.t from rfl, Ideal.span_singleton_pow]
    exact he i j
  have sep : ∀ a : x.A, (∀ m, a ∈ (Ideal.span {algebraMap x.A x.A x.t}) ^ m) → a = 0 :=
    fun a h => np_desc_sep a h
  have key : ∀ d : G.G₀, g.p₀ d = 1 → x.ρ d = 1 ∧ ∀ j, k.κ j d = 0 := by
    intro d hd
    have hdP : (d : G.Γ) ∈ PL l H := by
      rw [← hker, MonoidHom.mem_ker, ← Glob.Hom.coe_p₀, hd]
      rfl
    constructor
    · have h0 := (coc_pl l L G n x.A _ (x.ρX x.A) (fun _ => 0) H hH hη hl hR.1 hR.2.1 hR.2.2 hunip
        (fun i j N => IsLocallyConstant.const _) (fun a b => by simp)).2 d hdP
      apply Units.ext
      have hm : x.ρX x.A d = 1 :=
        Matrix.ext fun i j => sub_eq_zero.mp (sep _ (fun m => (h0 m i j).1))
      rw [hρ] at hm
      exact hm
    · intro j
      have hj := (coc_pl l L G n x.A _ (x.ρX x.A) (k.κ j) H hH hη hl hR.1 hR.2.1 hR.2.2 hunip
        (k.mem j).2.1 (k.mem j).2.2.1).2 d hdP
      exact Matrix.ext fun a b => sep _ (fun m => (hj m a b).2)
  have hkerρ : g.p₀.ker ≤ x.ρ.ker := fun d hd => (key d hd).1
  let e := QuotientGroup.quotientKerEquivOfSurjective g.p₀ g.p₀_surj
  refine ⟨⟨(QuotientGroup.lift g.p₀.ker x.ρ hkerρ).comp e.symm.toMonoidHom, fun a => ?_⟩,
    ⟨fun j b => k.κ j (Classical.choose (g.p₀_surj b)), fun j a => ?_⟩⟩
  · have hs : e.symm (g.p₀ a) = (QuotientGroup.mk a : G.G₀ ⧸ g.p₀.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift g.p₀.ker x.ρ hkerρ (e.symm (g.p₀ a)) = x.ρ a
    rw [hs]
    rfl
  · have hc : g.p₀ (Classical.choose (g.p₀_surj (g.p₀ a))) = g.p₀ a :=
      Classical.choose_spec (g.p₀_surj (g.p₀ a))
    set c := Classical.choose (g.p₀_surj (g.p₀ a))
    have hd : g.p₀ (c⁻¹ * a) = 1 := by rw [map_mul, map_inv, hc, inv_mul_cancel]
    have h3 := (k.mem j).2.2.1 c (c⁻¹ * a)
    rw [mul_inv_cancel_left, (key _ hd).2 j] at h3
    simp at h3
    exact h3.symm
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_open_normal {P Z : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    [TotallyDisconnectedSpace P] (K : Subgroup P) (hK : IsOpen (K : Set P)) (c : K → Z) (hc : IsLocallyConstant c) :
    ∃ V : OpenNormalSubgroup P, ∀ g g' : K, (g : P)⁻¹ * g' ∈ V → c g = c g' := by
  have hKc : IsClosed (K : Set P) := Subgroup.isClosed_of_isOpen K hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc.isCompact
  have hfin : (Set.range c).Finite := hc.range_finite
  have hS : ∀ z, ∃ W ∈ nhds (1 : P), ∀ x ∈ (Subtype.val '' (c ⁻¹' {z}) : Set P), ∀ w ∈ W,
      x * w ∈ (Subtype.val '' (c ⁻¹' {z}) : Set P) := by
    intro z
    have hcpt : IsCompact (Subtype.val '' (c ⁻¹' {z}) : Set P) :=
      (hc.isClosed_fiber z).isCompact.image continuous_subtype_val
    have ho : IsOpen (Subtype.val '' (c ⁻¹' {z}) : Set P) :=
      hK.isOpenMap_subtype_val _ (hc.isOpen_fiber z)
    open scoped Pointwise in
    obtain ⟨W, hW, hWS⟩ := compact_open_separated_mul_right hcpt ho subset_rfl
    open scoped Pointwise in
    exact ⟨W, hW, fun x hx w hw => hWS (Set.mul_mem_mul hx hw)⟩
  choose W hW hWS using hS
  have hI : (⋂ z ∈ Set.range c, W z) ∈ nhds (1 : P) := (Filter.biInter_mem hfin).2 fun z _ => hW z
  obtain ⟨O, hOI, hOo, h1O⟩ := mem_nhds_iff.1 hI
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
  refine ⟨H, fun g g' hgg => ?_⟩
  have h1 : (g : P)⁻¹ * g' ∈ W (c g) := Set.mem_iInter₂.1 (hOI (hH hgg)) (c g) ⟨g, rfl⟩
  have h2 : (g : P) ∈ Subtype.val '' (c ⁻¹' {c g}) := ⟨g, rfl, rfl⟩
  have h3 := hWS (c g) _ h2 _ h1
  rw [mul_inv_cancel_left] at h3
  obtain ⟨a', ha', he⟩ := h3
  have e : a' = g' := Subtype.ext he
  rw [← e]
  exact ha'.symm

theorem UpperTheory.V.Pa.eventually_factorization_compatible_with_local_maps :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (c : Λ.Ph0 → Z), IsLocallyConstant c → ∀ᶠ N in (Λ.U : Filter ℕ), ∀ (zN : (T.GN N).G₀ → Z) (z : Λ.G.G₀ → Z), (∀ g, zN (Λ.π0 N g) = c g) → (∀ g, z (Λ.πo0 g) = c g) → (∀ v g, zN ((T.GN N).φ v g) = z (Λ.G.φ v g)) ∧ (∀ w g, zN ((T.GN N).φu w g) = z (Λ.G.φu w g)) ∧ ∀ j, zN (T.ph N j) = z (Λ.ph j) ∧ zN (T.ta N j) = z (Λ.ta j) := by
  intro l _ L G0 T Λ Z c hc
  obtain ⟨V, hV⟩ := exists_open_normal _ Λ.Ph0_open c hc
  filter_upwards [Λ.φ_lim V, Λ.φu_lim V, Λ.ph_lim V, Λ.ta_lim V] with N h1 h2 h3 h4 zN z hN ho
  have key : ∀ (a : (T.GN N).G₀) (b : Λ.G.G₀), Close (Λ.π N) Λ.πo V.toSubgroup (a : (T.GN N).Γ) (b : Λ.G.Γ) →
      zN a = z b := by
    rintro a b ⟨g, g', ea, eb, hg⟩
    have m : g ∈ (Λ.G.η.comp Λ.πo).ker := (Λ.η_π N g).symm.trans (by rw [ea]; exact a.2)
    have m' : g' ∈ (Λ.G.η.comp Λ.πo).ker := show Λ.G.η (Λ.πo g') = 1 by rw [eb]; exact b.2
    have ea' : a = Λ.π0 N ⟨g, m⟩ := Subtype.ext ea.symm
    have eb' : b = Λ.πo0 ⟨g', m'⟩ := Subtype.ext eb.symm
    rw [ea', eb', hN, ho]
    exact hV _ _ hg
  exact ⟨fun v g => key _ _ (h1 v g), fun w g => key _ _ (h2 w g), fun j => ⟨key _ _ (h3 j), key _ _ (h4 j)⟩⟩
end
