module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import GroundTheory.AutomorphicForms.SmoothRep
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle345
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle342
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle343
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle330
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepFormulaF
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle344
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle326
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle336
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle346
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317

@[expose] public section

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeOpMul

open GroundTheory.Automorphic GlobalTheory.CompanionTheory.HeckeMult Zls

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_orbit_const {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : GlobalTheory.PRep.IsSmooth π)
    {K : Subgroup (GL (Fin N) k)} (hK : K ≤ KO k (Fin N)) {x y : V} (hy : ∀ g ∈ K, π g y = y)
    (hxy : ∀ l : Module.Dual ℂ V, (∀ g ∈ K, l ∘ₗ π g = l) → l x = l y)
    (f : Module.Dual ℂ V) (hf : ∀ g ∈ K, f (π g x) = f x) : f x = f y := by
  have hsm : GroundTheory.Automorphic.IsSmooth π := fun v => hπ v
  have hmem : x - y ∈ coinvariantsKer π K := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have := hxy (φ ∘ₗ (coinvariantsKer π K).mkQ) (fun g hg => by
      ext u
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
      congr 1
      exact (Submodule.Quotient.eq _).2 (sub_mem_coinvariantsKer hg u))
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at this
    rw [Submodule.Quotient.mk_sub, map_sub, this, sub_self]
  obtain ⟨U, hU, hUz⟩ := exists_nhds_cosetSum_eq_zero hsm hmem
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun W hW => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hW
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  haveI : TotallyDisconnectedSpace (GL (Fin N) k) :=
    ⟨(isTotallyDisconnected_of_image (f := fun g : GL (Fin N) k => g.val)
      GlobalTheory.SplitFlip.isEmbedding_val_GL.continuous.continuousOn
      GlobalTheory.SplitFlip.isEmbedding_val_GL.injective (isTotallyDisconnected_of_totallyDisconnectedSpace _))⟩
  obtain ⟨M, -, -, hMU, hnorm, hfin⟩ :=
    exists_normal_subgroup (K := KO k (Fin N)) GlobalTheory.SplitFlip.isCompact_KO GlobalTheory.SplitFlip.isOpen_KO hU
  haveI : (M.subgroupOf (KO k (Fin N))).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h2 : (M.subgroupOf (KO k (Fin N))).comap (Subgroup.inclusion hK) = M.subgroupOf K := by
    ext g
    simp [Subgroup.mem_subgroupOf]
  haveI : (M.subgroupOf K).FiniteIndex := by
    rw [← h2]
    refine ⟨?_⟩
    rw [Subgroup.index_comap]
    exact (inferInstance : (((M.subgroupOf (KO k (Fin N))).subgroupOf
      (Subgroup.inclusion hK).range).FiniteIndex)).index_ne_zero
  haveI : Finite (K ⧸ M.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (K ⧸ M.subgroupOf K) := Fintype.ofFinite _
  have h0 := hUz M hMU (fun g hg n hn => hnorm g (hK hg) n hn) inferInstance
  rw [map_sub, cosetSum_of_mem π (v := y) hy, sub_eq_zero, cosetSum_apply] at h0
  have h1 := congrArg f h0

  rw [map_sum, map_smul] at h1
  have h3 : ∀ q : K ⧸ M.subgroupOf K, f (π ((Quotient.out q : K) : GL (Fin N) k) x) = f x :=
    fun q => hf _ (Quotient.out q).2
  simp only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul] at h1
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h1

abbrev idl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) : Ideal 𝒪[k] := Ideal.span {unif k ^ m}

theorem isUnit_of_sub_one_mem {m : ℕ} (hm : 1 ≤ m) (s : 𝒪[k]) (hs : s - 1 ∈ idl k m) : IsUnit s := by
  by_contra hu
  have hmax : s ∈ IsLocalRing.maximalIdeal 𝒪[k] := hu
  have hpow : unif k ^ m ∈ IsLocalRing.maximalIdeal 𝒪[k] :=
    Ideal.pow_mem_of_mem _ (show unif k ∈ IsLocalRing.maximalIdeal 𝒪[k] from irreducible_unif.not_isUnit)
      m (by omega)
  have hle : idl k m ≤ IsLocalRing.maximalIdeal 𝒪[k] := (Ideal.span_singleton_le_iff_mem _).mpr hpow
  have h1m : (1 : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    have := Ideal.sub_mem _ hmax (hle hs)
    simpa using this
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top h1m

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) (A : Matrix (Fin N) (Fin N) 𝒪[k])
    (hA : CongOne (idl k m) A) :
    ∃ g ∈ Km k N m, g.val = A.map (algebraMap 𝒪[k] k) := by
  have hred : A.map (Ideal.Quotient.mk (idl k m)) = 1 := by
    ext i j
    have h := (Ideal.Quotient.eq (I := idl k m)).2 (hA i j)
    rw [Matrix.map_apply, h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit A.det := by
    refine isUnit_of_sub_one_mem hm _ ?_
    refine (Ideal.Quotient.eq (I := idl k m)).1 ?_
    have := RingHom.map_det (Ideal.Quotient.mk (idl k m)) A
    rw [this, map_one]
    have e : (Ideal.Quotient.mk (idl k m)).mapMatrix A = 1 := hred
    rw [e, Matrix.det_one]
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (Matrix.GeneralLinearGroup.mk'' A hdet),
    ⟨Matrix.GeneralLinearGroup.mk'' A hdet, ?_, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  exact Units.ext hred

theorem exists_cong_of_mem_Km {N m : ℕ} {g : GL (Fin N) k} (hg : g ∈ Km k N m) :
    ∃ A : Matrix (Fin N) (Fin N) 𝒪[k], CongOne (idl k m) A ∧ g.val = A.map (algebraMap 𝒪[k] k) := by
  obtain ⟨h, hh, rfl⟩ := hg
  refine ⟨h.val, fun i j => ?_, rfl⟩
  have h1 : (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (idl k m)) h).val = 1 := by
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hh
    rw [hh]; rfl
  have h2 := congrFun (congrFun h1 i) j
  refine (Ideal.Quotient.eq (I := idl k m)).1 ?_
  refine Eq.trans h2 ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem diagPow_val (N : ℕ) (a : Fin N → ℤ) :
    (diagPow k N a).val = Matrix.diagonal (fun i => (algebraMap 𝒪[k] k (unif k)) ^ (a i)) := by
  ext i j
  simp [diagPow, unifU, Matrix.diagonal_apply]

theorem diagPow_add (N : ℕ) (a b : Fin N → ℤ) :
    diagPow k N (a + b) = diagPow k N a * diagPow k N b := by
  have h0 : algebraMap 𝒪[k] k (unif k) ≠ 0 := (unifU k).ne_zero
  apply Units.ext
  rw [Units.val_mul, diagPow_val, diagPow_val, diagPow_val, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp [zpow_add₀ h0]

theorem exists_split {N m : ℕ} (hm : 1 ≤ m) {a b : Fin N → ℤ} (ha : Antitone a) (hb : Antitone b)
    {g : GL (Fin N) k} (hg : g ∈ Km k N m) :
    ∃ p ∈ Km k N m, ∃ l ∈ Km k N m, ∃ q ∈ Km k N m, ∃ r ∈ Km k N m,
      g = p * l ∧ diagPow k N a * p = q * diagPow k N a ∧ l * diagPow k N b = diagPow k N b * r := by
  have h0 : algebraMap 𝒪[k] k (unif k) ≠ 0 := (unifU k).ne_zero
  obtain ⟨A, hA, hgA⟩ := exists_cong_of_mem_Km hg
  obtain ⟨U, L, hU, hL, hUt, hLt, rfl⟩ := exists_upper_lower _ (isUnit_of_sub_one_mem hm) N A hA
  obtain ⟨Vq, hVq, hVe⟩ := conj_upper (K := k) (unif k) h0 a ha U hU hUt
  obtain ⟨Wr, hWr, hWe⟩ := conj_lower (K := k) (unif k) h0 b hb L hL hLt
  obtain ⟨p, hp, hpv⟩ := exists_mem_Km hm U hU
  obtain ⟨l, hl, hlv⟩ := exists_mem_Km hm L hL
  obtain ⟨q, hq, hqv⟩ := exists_mem_Km hm Vq hVq
  obtain ⟨r, hr, hrv⟩ := exists_mem_Km hm Wr hWr
  refine ⟨p, hp, l, hl, q, hq, r, hr, Units.ext ?_, Units.ext ?_, Units.ext ?_⟩
  · rw [hgA, Units.val_mul, hpv, hlv, Matrix.map_mul]
  · rw [Units.val_mul, Units.val_mul, hpv, hqv, diagPow_val, hVe]
  · rw [Units.val_mul, Units.val_mul, hlv, hrv, diagPow_val, hWe]

theorem Km_le_KO (N m : ℕ) : Km k N m ≤ KO k (Fin N) := by
  rintro _ ⟨h, -, rfl⟩
  exact ⟨h, rfl⟩

theorem isHeckeOp_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ m : ℕ, 1 ≤ m → ∀ (a b : Fin N → ℤ), Antitone a → Antitone b → ∀ (T T' : Module.End ℂ (fixed π (Zls.Km k N m))), Zls.IsHeckeOp π m (Zls.diagPow k N a) T → Zls.IsHeckeOp π m (Zls.diagPow k N b) T' → Zls.IsHeckeOp π m (Zls.diagPow k N (a + b)) (T * T') := by
  intro k _ _ _ _ N V _ _ π hπ m hm a b ha hb T T' hT hT' v l hl
  have hfix : ∀ (w : fixed π (Km k N m)), ∀ g ∈ Km k N m, π g (w : V) = w := by
    intro w g hg
    have := w.2 ⟨g, hg⟩
    simpa using this
  have hlg : ∀ g ∈ Km k N m, ∀ u, l (π g u) = l u := fun g hg u =>
    congrArg (fun t : Module.Dual ℂ V => t u) (hl g hg)
  have key := eq_of_orbit_const π hπ (Km_le_KO N m) (x := π (diagPow k N b) (v : V))
    (y := ((T' v : fixed π (Km k N m)) : V)) (hfix _)
    (fun l' hl' => hT' v l' hl') (l ∘ₗ π (diagPow k N a)) (by
      intro g hg
      obtain ⟨p, hp, l0, hl0, q, hq, r, hr, rfl, e1, e2⟩ := exists_split hm ha hb hg
      simp only [LinearMap.comp_apply]
      calc l (π (diagPow k N a) (π (p * l0) (π (diagPow k N b) (v : V))))
          = l (π (diagPow k N a * p * (l0 * diagPow k N b)) (v : V)) := by
            simp only [map_mul, Module.End.mul_apply]
        _ = l (π q (π (diagPow k N a) (π (diagPow k N b) (π r (v : V))))) := by
            rw [e1, e2]
            simp only [map_mul, Module.End.mul_apply]
        _ = l (π (diagPow k N a) (π (diagPow k N b) (v : V))) := by
            rw [hlg q hq, hfix v r hr])
  simp only [LinearMap.comp_apply] at key
  rw [diagPow_add, map_mul, Module.End.mul_apply, key]
  exact hT (T' v) l hl

end GlobalTheory.CompanionTheory.HeckeOpMul

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.SegDualPrec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section

variable (hc : ∀ x : IrrGL (k := k), x.IsCusp → (dualCl x).IsCusp)

include hc

theorem segDual_eq (Δ : Segment k) : segDual Δ =
    Segment.ofFirst ((dualCl Δ.first).nu (1 - (Δ.len : ℂ))) ((hc _ Δ.isCusp_first).nu _) Δ.len Δ.len_pos :=
  dite_eq_left (hc _ Δ.isCusp_first)

theorem first_segDual (Δ : Segment k) : (segDual Δ).first = (dualCl Δ.first).nu (1 - (Δ.len : ℂ)) := by
  rw [segDual_eq hc]; rfl

theorem len_segDual (Δ : Segment k) : (segDual Δ).len = Δ.len := by
  rw [segDual_eq hc]; rfl

variable (hn : ∀ (x : IrrGL (k := k)) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s))

include hn

theorem carrier_segDual (Δ : Segment k) : (segDual Δ).carrier = dualCl '' Δ.carrier := by
  ext x
  simp only [Set.mem_image, Segment.mem_carrier, first_segDual hc, len_segDual hc, IrrGL.nu_nu]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨_, ⟨Δ.len - 1 - a, by omega, rfl⟩, ?_⟩
    rw [hn]
    congr 1
    have h1 : a + 1 ≤ Δ.len := ha
    have h2 : ((Δ.len - 1 - a : ℕ) : ℂ) = (Δ.len : ℂ) - 1 - a := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [h2]
    ring
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨Δ.len - 1 - b, by omega, ?_⟩
    rw [hn]
    congr 1
    have h1 : b + 1 ≤ Δ.len := hb
    have h2 : ((Δ.len - 1 - b : ℕ) : ℂ) = (Δ.len : ℂ) - 1 - b := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [h2]
    ring

variable (hd : ∀ x : IrrGL (k := k), dualCl (dualCl x) = x)

include hd

theorem dualCl_injective : Function.Injective (dualCl : IrrGL (k := k) → IrrGL (k := k)) :=
  Function.LeftInverse.injective hd

theorem segDual_segDual (Δ : Segment k) : segDual (segDual Δ) = Δ := by
  refine Segment.ext_first ?_ (by rw [len_segDual hc, len_segDual hc])
  rw [first_segDual hc, first_segDual hc, len_segDual hc, hn, hd, IrrGL.nu_nu]
  simp

theorem linked_segDual {Δ Δ' : Segment k} (h : Δ.Linked Δ') : (segDual Δ).Linked (segDual Δ') := by
  obtain ⟨⟨Γ, hΓ⟩, h1, h2⟩ := h
  have hi := dualCl_injective hc hn hd
  refine ⟨⟨segDual Γ, ?_⟩, ?_, ?_⟩
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, carrier_segDual hc hn, hΓ, Set.image_union]
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, Set.image_subset_image_iff hi]
    exact h1
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, Set.image_subset_image_iff hi]
    exact h2

theorem precedes_segDual {Δ Δ' : Segment k} (h : Δ'.Precedes Δ) : (segDual Δ).Precedes (segDual Δ') := by
  obtain ⟨hl, j, hj, hf⟩ := h
  refine ⟨linked_segDual hc hn hd hl.symm, ?_⟩
  have hlen : Δ'.len < j + Δ.len := by
    by_contra hle
    refine hl.2.2 fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hx
    refine Segment.mem_carrier.2 ⟨j + a, by omega, ?_⟩
    rw [hf, IrrGL.nu_nu]
    push_cast
    rfl
  refine ⟨j + Δ.len - Δ'.len, by omega, ?_⟩
  rw [first_segDual hc, first_segDual hc, hf, hn, IrrGL.nu_nu, IrrGL.nu_nu]
  congr 1
  rw [Nat.cast_sub hlen.le]
  push_cast
  ring

theorem segDual_precedes_iff (Δ Δ' : Segment k) : (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := by
  refine ⟨fun h => ?_, precedes_segDual hc hn hd⟩
  have := precedes_segDual hc hn hd h
  rwa [segDual_segDual hc hn hd, segDual_segDual hc hn hd] at this

end

theorem segDual_precedes : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ Δ' : Segment k),
    (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := by
  intro k _ _ _ _ hA Δ Δ'
  have hadm (x : IrrGL (k := k)) : IsAdmissible x.rep :=
    hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr
  have hirr (x : IrrGL (k := k)) : (contra x.rep).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible
      (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (hadm x) x.2.rep.irr
  have hdual (x : IrrGL (k := k)) :
      dualCl x = IrrGL.of (contra x.rep) (isSmooth_contra _) (hirr x) :=
    dite_eq_left (hirr x)
  have hc (x : IrrGL (k := k)) (hx : x.IsCusp) : (dualCl x).IsCusp := by
    rw [hdual x, IrrGL.isCusp_of]
    exact ⟨hx.1, GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k x.1 _ _
      (GlobalTheory.CompanionTheory.DualCusp.isSupercuspidal_contra
        (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (hadm x)
        (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k x.1 _ _ hx.2))⟩
  have hn (x : IrrGL (k := k)) (s : ℂ) : dualCl (x.nu s) = (dualCl x).nu (-s) := by
    have hs : IsSmoothChar (absPow k s) := isSmoothChar_absPow s
    have hs_neg : IsSmoothChar (absPow k (-s)) := isSmoothChar_absPow (-s)
    have hmul : absPow k s * absPow k (-s) = 1 := by
      rw [absPow_neg, mul_inv_cancel]
    obtain ⟨e⟩ := GlobalTheory.CompanionTheory.ZcDual.nonempty_equiv_contra_twist
      hA x.rep x.2.rep.smooth x.2.rep.irr hs hs_neg hmul
    rw [hdual (x.nu s), hdual x]
    change IrrGL.of (contra (x.nu s).rep) _ _ =
      (IrrGL.of (contra x.rep) _ _).tw (absPow k (-s)) hs_neg
    rw [IrrGL.tw_of]
    exact IrrGL.of_eq_of.mpr ⟨(GlobalTheory.ContraRefl.contraEquiv (x.twEquiv _ hs)).trans e.symm⟩
  have hd (x : IrrGL (k := k)) : dualCl (dualCl x) = x := by
    rw [hdual x, hdual]
    conv_rhs => rw [← IrrGL.of_rep x]
    exact IrrGL.of_eq_of.mpr ⟨
      (GlobalTheory.ContraRefl.contraEquiv (IrrGL.equivOf (contra x.rep) _ _)).trans
        (GlobalTheory.ContraRefl.evEquiv
          (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (hadm x)).symm⟩
  exact segDual_precedes_iff hc hn hd Δ Δ'

end GlobalTheory.CompanionTheory.SegDualPrec
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

theorem _root_.GlobalTheory.T.dual_class_involutive : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)), dualCl (dualCl x) = x := by
  first | exact @GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl | exact GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl | (intros; apply GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.jacquet_multiplicity_of_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), Nonempty (π.Equiv σ) → jm x hd π = jm x hd σ := by
  first | exact @GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv | exact GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv | (intros; apply GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.jacquet_multiplicity_subquotient_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (y : Fin h → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (P : Representation ℂ (GL (Fin N) k) W) (hP : IsSmooth P) (h : IsSubquotient π P), jm y hy π ≤ jm y hy P := by
  first | exact @GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient | exact GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

theorem _root_.GlobalTheory.T.langlands_classification_order_free_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k → ∀ (𝔭 : Multiset (Segment k)) {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), IsL 𝔭 π → IsL 𝔭 σ → Nonempty (π.Equiv σ) := by
  first | exact @GlobalTheory.CompanionTheory.LUniq.isL_unique | exact GlobalTheory.CompanionTheory.LUniq.isL_unique | (intros; apply GlobalTheory.CompanionTheory.LUniq.isL_unique <;> assumption)
end

section


theorem _root_.GlobalTheory.T.sobolev_space_preserved : PositivityTheory.RgBcC.Fc.PresSob := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.presSob | exact GlobalTheory.CompanionTheory.PresSobA.presSob | (intros; apply GlobalTheory.CompanionTheory.PresSobA.presSob <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mollifier_approximation_hilbert : PositivityTheory.RgDs.Hilb.StepMoll := by
  first | exact @GlobalTheory.CompanionTheory.HilbMoll.stepMoll | exact GlobalTheory.CompanionTheory.HilbMoll.stepMoll | (intros; apply GlobalTheory.CompanionTheory.HilbMoll.stepMoll <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

theorem _root_.GlobalTheory.T.psi_preserves_isomorphism : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A B : MRep k n), MIso A B → GIso (psiN A) (psiN B) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN | exact GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

theorem _root_.GlobalTheory.T.restriction_product_rank_zero_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n), IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' | exact GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' | (intros; apply GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.modulus_characters_product_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i (t + 1)),
  ((dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) : ℂˣ) : ℂ) * ((dpow (t + 1) 1 (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ) *
    (((dpowM i (1 / 2) (pgProj k i (t + 1) h).1 : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.DetPG.exponents_cancel | exact GlobalTheory.CompanionTheory.BZPhiPG.DetPG.exponents_cancel | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.DetPG.exponents_cancel <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.modulus_mirabolic_block_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : ℝ) (h : MirabolicParabolic k (i + 1) t), dpowM ((i + 1) + t) s (h : Mir k ((i + 1) + t)) = dpow (i + 1) s (gpProj k (i + 1) t h).1 * dpow (t + 1) s (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.dpowM_hgp | exact GlobalTheory.CompanionTheory.BZPhiPG.dpowM_hgp | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.dpowM_hgp <;> assumption)
end
