module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.mSplitAlg_basis :
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (n : ℕ) (R : Type) [CommRing R] (P : κ → Polynomial R), (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) →
      ∃ b : Module.Basis (κ → ∀ i : Fin n, Fin (n - i)) R (MSplitAlg P n), ∀ c, b c = ∏ j, ∏ i, MSplitAlg.root P n j i ^ (c j i : ℕ) := by
  intro κ _ _ n R _ P hm hd
  have hb := fun j => (UpperTheory.V.AlgebraTools.splitAlg_basis n R (P j) (hm j) (hd j)).1
  choose bj hbj using hb
  let f : ∀ j, SplitAlg (P j) n →ₐ[R] MSplitAlg P n := fun j =>
    SplitAlg.lift (P j) n (MSplitAlg.root P n j) (MSplitAlg.prod_root P n j)
  let M : (∀ j, SplitAlg (P j) n) →ₘₗ[R] MSplitAlg P n :=
    (MultilinearMap.mkPiAlgebra R κ (MSplitAlg P n)).compLinearMap (fun j => (f j).toLinearMap)
  have hM : ∀ x, M x = ∏ j, f j (x j) := fun x => by
    simp [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  let ψ : (⨂[R] j, SplitAlg (P j) n) →ₐ[R] MSplitAlg P n :=
    PiTensorProduct.liftAlgHom M (by rw [hM]; simp)
      (fun x y => by rw [hM, hM, hM]; simp [Finset.prod_mul_distrib])
  have hψt : ∀ x, ψ (PiTensorProduct.tprod R x) = ∏ j, f j (x j) := fun x => by
    simp [ψ, hM]
  have hψs : ∀ j x, ψ (PiTensorProduct.singleAlgHom j x) = f j x := fun j x => by
    rw [PiTensorProduct.singleAlgHom_apply, hψt,
      Fintype.prod_eq_single j (fun k hk => by simp [Pi.mulSingle_eq_of_ne hk])]
    simp
  let φ : MSplitAlg P n →ₐ[R] (⨂[R] j, SplitAlg (P j) n) :=
    MSplitAlg.lift P n (fun j i => PiTensorProduct.singleAlgHom j (SplitAlg.root (P j) n i)) (fun j => by
      have := congrArg (Polynomial.map
        (PiTensorProduct.singleAlgHom (R := R) (A := fun j => SplitAlg (P j) n) j).toRingHom)
        (SplitAlg.prod_root (P j) n)
      simp only [Polynomial.map_prod, Polynomial.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe] at this
      exact this)
  have h1 : ψ.comp φ = AlgHom.id R (MSplitAlg P n) := MSplitAlg.hom_ext P n (fun j i => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, φ, MSplitAlg.lift_root, hψs, f, SplitAlg.lift_root])
  have h2 : φ.comp ψ = AlgHom.id R _ := PiTensorProduct.algHom_ext (fun j => SplitAlg.hom_ext (P j) n (fun i => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hψs, f, SplitAlg.lift_root, φ, MSplitAlg.lift_root]))
  let e : MSplitAlg P n ≃ₐ[R] (⨂[R] j, SplitAlg (P j) n) := AlgEquiv.ofAlgHom φ ψ h2 h1
  refine ⟨(Basis.piTensorProduct bj).map e.symm.toLinearEquiv, fun c => ?_⟩
  rw [Module.Basis.map_apply, Basis.piTensorProduct_apply]
  show ψ _ = _
  rw [hψt]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [hbj j (c j), map_prod]
  simp only [map_pow, f, SplitAlg.lift_root]
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.regular_quotient_cotInd :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      IsRegularLocalRing (R ⧸ Ideal.span (Set.range x)) ∧
      ringKrullDim (R ⧸ Ideal.span (Set.range x)) + (Fintype.card κ : ℕ) = ringKrullDim R ∧
      (Ideal.span (Set.range x)).IsPrime := by
  intro R _ _ κ _ x hx
  classical
  obtain ⟨s, y, -, hs, hc⟩ := cotInd_extend R κ x hx
  rw [Set.Sum.elim_range] at hs
  have hd : ringKrullDim R = ((Fintype.card κ + s : ℕ) : WithBot ℕ∞) := by
    rw [hc, IsRegularLocalRing.spanFinrank_maximalIdeal]
  set I := Ideal.span (Set.range x) with hI
  have hle : I ≤ maximalIdeal R := by
    rw [← hs]
    exact Ideal.span_mono Set.subset_union_left
  have hne : I ≠ ⊤ := fun h => Ideal.IsPrime.ne_top' (top_le_iff.mp (h ▸ hle))
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ I) := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (y i)) = maximalIdeal (R ⧸ I) := by
    rw [← hmax, ← hs, Ideal.span_union, Ideal.map_sup, ← hI, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hfin : ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (s : ℕ) := by
    rw [← hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R ⧸ I)
      (Set.finite_range fun i => Ideal.Quotient.mk I (y i))
    have h2 : (Set.range fun i => Ideal.Quotient.mk I (y i)).ncard ≤ s := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
    exact_mod_cast h1.trans h2
  have hdim : ((s : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
    have h1 := ringKrullDim_le_ringKrullDim_quotient_add_encard (Set.range x)
      (by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
        rintro _ ⟨k, rfl⟩
        exact hx.mem k)
    rw [hd] at h1
    have h2 : (Set.range x).encard ≤ (Fintype.card κ : ℕ∞) := by
      rw [← Set.image_univ]
      refine (Set.encard_image_le _ _).trans ?_
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    have hnb : ringKrullDim (R ⧸ I) ≠ ⊥ := ringKrullDim_ne_bot
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hnb
    rw [← hn] at h1 ⊢
    have h3 : (Fintype.card κ : ℕ∞) + (s : ℕ∞) ≤ n + (Set.range x).encard := by
      exact_mod_cast h1
    have h4 : (s : ℕ∞) + (Fintype.card κ : ℕ∞) ≤ n + (Fintype.card κ : ℕ∞) := by
      rw [add_comm]
      exact h3.trans (by gcongr)
    have h5 : (s : ℕ∞) ≤ n := (ENat.add_le_add_iff_right (ENat.natCast_ne_top _)).mp h4
    exact_mod_cast h5
  have hreg : IsRegularLocalRing (R ⧸ I) := .of_spanFinrank_maximalIdeal_le _ (hfin.trans hdim)
  have heq : ringKrullDim (R ⧸ I) = (s : ℕ) :=
    le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal _).trans hfin) hdim
  refine ⟨hreg, ?_, ?_⟩
  · rw [heq, hd, add_comm]
    push_cast
    rfl
  · exact (Ideal.Quotient.isDomain_iff_prime I).1 (GlobalTheory.isDomain_of_isRegularLocalRing _)
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem exists_sum_of_mem_span_smul_top {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    {n : ℕ} (g : Fin n → R) (x : M) (hx : x ∈ (Ideal.span (Set.range g) • ⊤ : Submodule R M)) :
    ∃ q : Fin n → M, x = ∑ c, g c • q c := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hr
    refine ⟨fun i => c i • m, ?_⟩
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  · rintro x y ⟨q, rfl⟩ ⟨q', rfl⟩
    exact ⟨fun i => q i + q' i, by simp [smul_add, Finset.sum_add_distrib]⟩

theorem UpperTheory.V.AlgebraTools.ULim.mem_smul_top_iff :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (a : Ideal R), a.FG → Antitone I →
      ∀ p : ∀ i, M i, ULim.mk F I M p ∈ (a • ⊤ : Submodule R (ULim F I M)) ↔
        ∀ j, ∀ᶠ N in F, p N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N)) := by
  intro R _ F hF I M _ _ a ha hI p
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 ha
  have hg' : Ideal.span (Set.range g) = a := hg
  have hga : ∀ c, g c ∈ a := fun c => hg' ▸ Ideal.subset_span ⟨c, rfl⟩
  constructor
  · intro hp j
    rw [← hg'] at hp
    obtain ⟨q, hq⟩ := exists_sum_of_mem_span_smul_top g _ hp
    choose q' hq' using fun c => ULim.mk_surjective F I M (q c)
    have h0 : ULim.mk F I M (p - ∑ c, g c • q' c) = 0 := by

      rw [map_sub, map_sum, hq]
      simp only [map_smul, hq', sub_self]
    filter_upwards [ULim.mk_eq_zero.1 h0 j] with N hN
    have h1 : (∑ c, g c • q' c) N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N)) := by
      rw [Finset.sum_apply]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem_smul (Ideal.mem_sup_left (hga c)) Submodule.mem_top
    have h2 := Submodule.add_mem ((a ⊔ I j) • ⊤ : Submodule R (M N)) (Submodule.smul_mono_left (le_sup_right : I j ≤ a ⊔ I j) hN) h1
    simpa using h2
  · intro hp
    obtain ⟨ν, hν, hP⟩ := exists_diag F hF
      (fun j N => p N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N))) hp
    have key : ∀ N, ∃ q : Fin n → M N, p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N)) →
        p N - ∑ c, g c • q c ∈ (I (ν N) • ⊤ : Submodule R (M N)) := by
      intro N
      by_cases h : p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N))
      · have h' := h
        rw [Submodule.sup_smul] at h'
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h'
        rw [← hg'] at hy
        obtain ⟨q, hq⟩ := exists_sum_of_mem_span_smul_top g _ hy
        refine ⟨q, fun _ => ?_⟩
        rw [← hq, ← hyz, add_sub_cancel_left]
        exact hz
      · exact ⟨0, fun h' => absurd h' h⟩
    choose q hq using key
    have h0 : ULim.mk F I M (p - ∑ c, g c • fun N => q N c) = 0 := by
      refine ULim.mk_eq_zero.2 fun j => ?_
      filter_upwards [hP, hν.eventually_ge_atTop j] with N hN hj
      have := Submodule.smul_mono_left (hI hj) (hq N (hN _ le_rfl))
      simpa [Finset.sum_apply] using this
    rw [map_sub, sub_eq_zero] at h0

    rw [h0, map_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem_smul (hga c) Submodule.mem_top
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem leviSum_split {G : Type} [Group G] {I : Subgroup G} (F : LeviFact I) {x y : G}
    (hx : x ∈ F.Uf) (hy : y ∈ F.Mf) (h : x * y ∈ I) : x ∈ I ∧ y ∈ I := by
  obtain ⟨u, hu, k, hk, l, hl, he⟩ := F.fact _ h
  rw [Subgroup.mem_inf] at hu hk hl
  have hyl : y * l * y⁻¹ ∈ F.Lf := F.M_L y hy l hl.1
  have key : (x⁻¹ * u) * (k * y⁻¹) * (y * l * y⁻¹) = 1 := by
    calc (x⁻¹ * u) * (k * y⁻¹) * (y * l * y⁻¹) = x⁻¹ * (u * k * l) * y⁻¹ := by group
      _ = 1 := by rw [← he]; group
  obtain ⟨h1, h2⟩ := F.uniq _ (F.Uf.mul_mem (F.Uf.inv_mem hx) hu.1) _
    (F.Mf.mul_mem hk.1 (F.Mf.inv_mem hy)) _ hyl key
  have hxu : x = u := inv_mul_eq_one.mp h1
  have hyk : y = k := (mul_inv_eq_one.mp h2).symm
  exact ⟨hxu ▸ hu.2, hyk ▸ hk.2⟩

theorem UpperTheory.V.AlgebraTools.leviSum :
    ∀ (G : Type) [Group G] (I : Subgroup G) (F : LeviFact I) (m : G), HeckePair I → F.Pos m → ∀ (s : Finset G), (∀ a ∈ s, ∃ j ∈ F.Mf ⊓ I, ∃ j' ∈ F.Mf ⊓ I, a = j * m * j') → (∀ j ∈ F.Mf ⊓ I, ∃! a, a ∈ s ∧ a⁻¹ * (j * m) ∈ I) → ∀ (r : G → Finset G), (∀ a ∈ s, (∀ u ∈ r a, u ∈ F.Uf ⊓ I) ∧ ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ r a ∧ a⁻¹ * (u⁻¹ * x) * a ∈ I) → ∀ q : G ⧸ I, q ∈ MulAction.orbit I (m : G ⧸ I) ↔ ∃ p : G × G, (p.1 ∈ s ∧ p.2 ∈ r p.1 ∧ ((p.2 * p.1 : G) : G ⧸ I) = q) ∧ ∀ p' : G × G, p'.1 ∈ s → p'.2 ∈ r p'.1 → ((p'.2 * p'.1 : G) : G ⧸ I) = q → p' = p := by
  intro G _ I F m _ hm s hs hs1 r hr q
  have hmM : m ∈ F.Mf := hm.1
  have hsm : ∀ (g : I) (x : G), g • (x : G ⧸ I) = (((g : G) * x : G) : G ⧸ I) := fun g x => rfl
  have huniq : ∀ a ∈ s, ∀ a' ∈ s, ∀ v ∈ r a, ∀ v' ∈ r a',
      ((v' * a' : G) : G ⧸ I) = ((v * a : G) : G ⧸ I) → a' = a ∧ v' = v := by
    intro a ha a' ha' v hv v' hv' heq
    have hvI := Subgroup.mem_inf.mp ((hr a ha).1 v hv)
    have hv'I := Subgroup.mem_inf.mp ((hr a' ha').1 v' hv')
    have hd : (v * a)⁻¹ * (v' * a') ∈ I := QuotientGroup.eq.mp heq.symm
    obtain ⟨j, hj, j', hj', hja⟩ := hs a ha
    obtain ⟨j1, hj1, j1', hj1', hja'⟩ := hs a' ha'
    rw [Subgroup.mem_inf] at hj hj' hj1 hj1'
    have hw : j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹ ∈ F.Uf :=
      F.M_U _ (F.Mf.inv_mem hj.1) _ (F.Uf.mul_mem (F.Uf.inv_mem hvI.1) hv'I.1)
    have hX : m⁻¹ * (j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹) * m⁻¹⁻¹ ∈ F.Uf :=
      F.M_U _ (F.Mf.inv_mem hmM) _ hw
    have hY : m⁻¹ * (j⁻¹ * j1) * m ∈ F.Mf :=
      F.Mf.mul_mem (F.Mf.mul_mem (F.Mf.inv_mem hmM) (F.Mf.mul_mem (F.Mf.inv_mem hj.1) hj1.1)) hmM
    have hXY : m⁻¹ * (j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹) * m⁻¹⁻¹ * (m⁻¹ * (j⁻¹ * j1) * m) ∈ I := by
      have he : m⁻¹ * (j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹) * m⁻¹⁻¹ * (m⁻¹ * (j⁻¹ * j1) * m)
          = j' * ((v * a)⁻¹ * (v' * a')) * j1'⁻¹ := by
        rw [hja, hja']
        group
      rw [he]
      exact I.mul_mem (I.mul_mem hj'.2 hd) (I.inv_mem hj1'.2)
    have hYI := (leviSum_split F hX hY hXY).2
    have haa : a' = a := by
      refine (hs1 j1 (Subgroup.mem_inf.mpr hj1)).unique ⟨ha', ?_⟩ ⟨ha, ?_⟩
      · have he : a'⁻¹ * (j1 * m) = j1'⁻¹ := by
          rw [hja']
          group
        rw [he]
        exact I.inv_mem hj1'.2
      · have he : a⁻¹ * (j1 * m) = j'⁻¹ * (m⁻¹ * (j⁻¹ * j1) * m) := by
          rw [hja]
          group
        rw [he]
        exact I.mul_mem (I.inv_mem hj'.2) hYI
    subst haa
    refine ⟨rfl, ?_⟩
    refine ((hr a' ha).2 v' (Subgroup.mem_inf.mpr hv'I)).unique ⟨hv', ?_⟩ ⟨hv, ?_⟩
    · have he : a'⁻¹ * (v'⁻¹ * v') * a' = 1 := by group
      rw [he]
      exact I.one_mem
    · have he : a'⁻¹ * (v⁻¹ * v') * a' = (v * a')⁻¹ * (v' * a') := by group
      rw [he]
      exact hd
  constructor
  · intro hq
    obtain ⟨⟨i, hi⟩, rfl⟩ := MulAction.mem_orbit_iff.mp hq
    obtain ⟨u', hu', j, hj, l, hl, hil⟩ := F.fact i hi
    obtain ⟨a, ⟨ha, hajm⟩, -⟩ := hs1 j hj
    obtain ⟨v, ⟨hv, hvu⟩, -⟩ := (hr a ha).2 u' hu'
    rw [Subgroup.mem_inf] at hl hj hu'
    have hq : (⟨i, hi⟩ : I) • (m : G ⧸ I) = ((v * a : G) : G ⧸ I) := by
      rw [hsm]
      apply QuotientGroup.eq.mpr
      have he : ((i : G) * m)⁻¹ * (v * a)
          = (m⁻¹ * l * m)⁻¹ * (a⁻¹ * (j * m))⁻¹ * (a⁻¹ * (v⁻¹ * u') * a)⁻¹ := by
        simp only [hil]
        group
      rw [he]
      exact I.mul_mem (I.mul_mem (I.inv_mem (hm.2.2 l (Subgroup.mem_inf.mpr hl)))
        (I.inv_mem hajm)) (I.inv_mem hvu)
    rw [hq]
    refine ⟨(a, v), ⟨ha, hv, rfl⟩, ?_⟩
    intro p' hp1 hp2 hp3
    obtain ⟨h1, h2⟩ := huniq a ha p'.1 hp1 v hv p'.2 hp2 hp3
    exact Prod.ext h1 h2
  · rintro ⟨⟨a, v⟩, ⟨ha, hv, rfl⟩, -⟩
    obtain ⟨j, hj, j', hj', hja⟩ := hs a ha
    have hvI := Subgroup.mem_inf.mp ((hr a ha).1 v hv)
    rw [Subgroup.mem_inf] at hj hj'
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨v * j, I.mul_mem hvI.2 hj.2⟩, ?_⟩
    rw [hsm]
    apply QuotientGroup.eq.mpr
    have he : ((v * j : G) * m)⁻¹ * (v * a) = j' := by
      rw [hja]
      group
    simp only [he]
    exact hj'.2
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem swap_lt_iff {n : ℕ} (i j x y : Fin n) (h : (j : ℕ) = i + 1)
    (h1 : ¬ (x = i ∧ y = j)) (h2 : ¬ (x = j ∧ y = i)) :
    Equiv.swap i j x < Equiv.swap i j y ↔ x < y := by
  have key : ∀ z : Fin n, (z = i ∧ Equiv.swap i j z = j) ∨ (z = j ∧ Equiv.swap i j z = i) ∨
      (z ≠ i ∧ z ≠ j ∧ Equiv.swap i j z = z) := by
    intro z
    by_cases hi : z = i
    · left; subst hi; simp
    · by_cases hj : z = j
      · right; left; subst hj; simp
      · right; right; exact ⟨hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj⟩
  rcases key x with ⟨hx, ex⟩ | ⟨hx, ex⟩ | ⟨hx1, hx2, ex⟩ <;>
  rcases key y with ⟨hy, ey⟩ | ⟨hy, ey⟩ | ⟨hy1, hy2, ey⟩ <;>
  rw [ex, ey] <;> simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, ne_eq] at * <;>
  constructor <;> intro <;> omega

private theorem len_up {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) (h : (j : ℕ) = i + 1)
    (hw : w⁻¹ i < w⁻¹ j) : invLen (Equiv.swap i j * w) = invLen w + 1 := by
  have hij : i < j := by rw [Fin.lt_iff_val_lt_val]; omega
  show (Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ (Equiv.swap i j * w) p.2 < (Equiv.swap i j * w) p.1)).card =
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1)).card + 1
  rw [show Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ (Equiv.swap i j * w) p.2 < (Equiv.swap i j * w) p.1) =
    insert (w⁻¹ i, w⁻¹ j) (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1))
    from ?_]
  · apply Finset.card_insert_of_notMem
    simp [hij.le]
  · ext ⟨x, y⟩
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Prod.mk.injEq, Equiv.Perm.mul_apply]
    by_cases hxy : x = w⁻¹ i ∧ y = w⁻¹ j
    · obtain ⟨rfl, rfl⟩ := hxy
      simp [hij]
      exact hw
    · rw [or_iff_right hxy]
      apply and_congr_right
      intro hlt
      apply swap_lt_iff i j _ _ h
      · rintro ⟨h1, h2⟩
        have e1 : y = w⁻¹ i := by rw [← h1]; simp
        have e2 : x = w⁻¹ j := by rw [← h2]; simp
        subst e1 e2
        exact absurd hlt (not_lt.mpr hw.le)
      · rintro ⟨h1, h2⟩
        exact hxy ⟨by rw [← h2]; simp, by rw [← h1]; simp⟩

private theorem len_down {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) (h : (j : ℕ) = i + 1)
    (hw : w⁻¹ j < w⁻¹ i) : invLen (Equiv.swap i j * w) + 1 = invLen w := by
  have key := len_up (Equiv.swap i j * w) i j h
    (by simpa [_root_.mul_inv_rev, Equiv.swap_inv] using hw)
  rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at key
  exact key.symm

private theorem exists_desc {n : ℕ} (w : Equiv.Perm (Fin n)) (hw : w ≠ 1) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ w⁻¹ j < w⁻¹ i := by
  by_contra hne
  push_neg at hne
  apply hw
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    have hmono : StrictMono (⇑w⁻¹) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro k
      refine lt_of_le_of_ne (hne _ _ (by simp)) (fun e => ?_)
      exact absurd (w⁻¹.injective e) Fin.castSucc_lt_succ.ne
    have hid : (⇑w⁻¹) = id := (hmono.range_inj strictMono_id).1 (by simp)
    rw [← inv_eq_one]
    ext x
    simp [congrFun hid x]

theorem UpperTheory.V.AlgebraTools.lenStep :
    ∀ (n : ℕ) (w : Equiv.Perm (Fin n)), (∀ (i j : Fin n), (j : ℕ) = i + 1 → (w⁻¹ i < w⁻¹ j → invLen (Equiv.swap i j * w) = invLen w + 1) ∧ (w⁻¹ j < w⁻¹ i → invLen (Equiv.swap i j * w) + 1 = invLen w)) ∧ (invLen w = 0 → w = 1) ∧ (w ≠ 1 → ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ w⁻¹ j < w⁻¹ i) := by
  intro n w
  refine ⟨fun i j h => ⟨len_up w i j h, len_down w i j h⟩, fun h0 => ?_, exists_desc w⟩
  by_contra hw
  obtain ⟨i, j, h, hlt⟩ := exists_desc w hw
  have := len_down w i j h hlt
  omega
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.evaluation_unit_factor {A H E : Type} [CommRing A] [Semiring H] [Algebra A H] [Semiring E] [Algebra A E]
    (ev : H →ₐ[A] E) (a y z : H) (c : A) (u v w : Eˣ) (h : a * y = c • z) (hy : ev y = v) (hz : ev z = w)
    (hw : w = u * v) : ev a = c • (u : E) := by
  have h' := congrArg ev h
  rw [map_mul, map_smul, hy, hz, hw, Units.val_mul, ← smul_mul_assoc] at h'
  exact (Units.mul_left_inj _).1 h'

theorem UpperTheory.V.AlgebraTools.thetaTie :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (x : kˣ), IsUnif x → IsUnit (resCard k : A) → ∀ (b : UpperTheory.V.AlgebraTools.Hk.Bern n (resCard k : A) (HkAlg A (iwC k n ⊤))) (ev : HkAlg A (iwC k n ⊤) →ₐ[A] Module.End A (fixd ρ (iwC k n ⊤))) (θ : (Fin n → kˣ) →* (Module.End A (fixd ρ (iwC k n ⊤)))ˣ), (∀ g, ev (hT A (iwC k n ⊤) g) = hk ρ (iwC k n ⊤) g) → (∀ t, Dom t → (θ t : Module.End A (fixd ρ (iwC k n ⊤))) = hk ρ (iwC k n ⊤) (diagT k (Fin n) t)) → (∀ i : Fin n, b.th (MvPolynomial.X i) * hT A (iwC k n ⊤) (pw x (fund n i)) = ((resCard k : A) ^ (i : ℕ)) • hT A (iwC k n ⊤) (pw x (fund n ((i : ℕ) + 1)))) → ∀ i : Fin n, ev (b.th (MvPolynomial.X i)) = ((resCard k : A) ^ (i : ℕ)) • (θ (Pi.mulSingle i x) : Module.End A (fixd ρ (iwC k n ⊤))) := by
  intro k _ _ _ _ n A M _ _ _ ρ x hx _ b ev θ hev hθ hb i
  have hx1 : valuation k (x : k) ≤ 1 := by
    obtain ⟨p, -, hp⟩ := hx
    rw [← hp]
    exact p.2
  have hdom : ∀ m : ℕ, Dom (fun j : Fin n => x ^ fund n m j) := by
    intro m j l hjl
    have hjl' : (j : ℕ) ≤ (l : ℕ) := hjl
    simp only [fund]
    by_cases h1 : (l : ℕ) < m
    · have h2 : (j : ℕ) < m := lt_of_le_of_lt hjl' h1
      simp [h1, h2]
    · by_cases h2 : (j : ℕ) < m
      · simpa [h1, h2] using hx1
      · simp [h1, h2]
  have hsplit : (fun j : Fin n => x ^ fund n ((i : ℕ) + 1) j)
      = Pi.mulSingle i x * (fun j : Fin n => x ^ fund n (i : ℕ) j) := by
    funext j
    simp only [fund, Pi.mul_apply]
    by_cases hj : j = i
    · subst hj
      simp
    · have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Fin.ext h)
      rw [Pi.mulSingle_eq_of_ne hj, one_mul]
      by_cases h : (j : ℕ) < (i : ℕ)
      · have h' : (j : ℕ) < (i : ℕ) + 1 := by omega
        simp [h, h']
      · have h' : ¬ (j : ℕ) < (i : ℕ) + 1 := by omega
        simp [h, h']
  refine UpperTheory.V.AlgebraTools.evaluation_unit_factor ev _ _ _ _ _ (θ fun j : Fin n => x ^ fund n (i : ℕ) j)
    (θ fun j : Fin n => x ^ fund n ((i : ℕ) + 1) j) (hb i) ?_ ?_ ?_
  · exact (hev _).trans (hθ _ (hdom _)).symm
  · exact (hev _).trans (hθ _ (hdom _)).symm
  · rw [hsplit]
    exact map_mul θ _ _
end
