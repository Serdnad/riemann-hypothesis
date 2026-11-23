module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCard
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle146
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle164
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle106
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle155
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle176
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle154
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Complex
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.IdealFund

open GlobalTheory.HomCovolume

theorem exists_lat (K : Type) [Field K] [NumberField K] (hK : IsTotallyComplex K) (ι : Type) [Fintype ι]
    (σ : ι → (K →+* ℂ)) (hσ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w)
    (a : FractionalIdeal (𝓞 K)⁰ K) (ha : a ≠ 0) :
    ∃ L : Submodule ℤ (ι → ℂ), (∀ z, z ∈ L ↔ ∃ y ∈ a, ∀ v, z v = σ v y) ∧
      HasCov volume L ((FractionalIdeal.absNorm a : ℝ) * Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) := by
  obtain ⟨L, hL, hcov⟩ := exists_idealLat K hK a ha
  let g : ι ≃ InfinitePlace K := Equiv.ofBijective (fun v => InfinitePlace.mk (σ v))
    ((Function.bijective_iff_existsUnique _).2 hσ)
  have hg : ∀ w, InfinitePlace.mk (σ (g.symm w)) = w := fun w => g.apply_symm_apply w
  have hκ : ∀ w : InfinitePlace K, ∃ κ : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ t, κ (σ (g.symm w) t) = w.embedding t := by
    intro w
    have h1 : InfinitePlace.mk (σ (g.symm w)) = InfinitePlace.mk w.embedding := by
      rw [hg, InfinitePlace.mk_embedding]
    rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
    · exact ⟨LinearIsometryEquiv.refl _ _, fun t => by rw [← h]; rfl⟩
    · exact ⟨Complex.conjLIE, fun t => by rw [← h]; rfl⟩
  choose κ hκ using hκ
  let e₀ : (ι → ℂ) ≃ₗ[ℝ] (InfinitePlace K → ℂ) :=
    { toFun := fun z w => κ w (z (g.symm w)), invFun := fun x v => (κ (g v)).symm (x (g v))
      map_add' := fun _ _ => funext fun w => by simp
      map_smul' := fun _ _ => funext fun w => by simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
      left_inv := fun _ => funext fun v => by simp
      right_inv := fun _ => funext fun w => by simp }
  have hcard : Fintype.card ι = Fintype.card (InfinitePlace K) := Fintype.card_congr g
  have hmp : MeasurePreserving e₀.toContinuousLinearEquiv volume volume := by
    refine measurePreserving_of_ball _ _ _ (fun x => ?_) ?_
    · change ‖fun w => κ w (x (g.symm w))‖ ≤ 1 ↔ _
      simp only [pi_norm_le_iff_of_nonneg zero_le_one, LinearIsometryEquiv.norm_map]
      exact ⟨fun h v => by simpa using h (g v), fun h w => h _⟩
    · simp [volume_pi_closedBall _ zero_le_one, hcard]
  refine ⟨ZLattice.comap ℝ L e₀.toContinuousLinearEquiv.toLinearMap, fun z => ?_, ?_⟩
  · change e₀ z ∈ L ↔ _
    rw [hL]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h v => ?_, fun h w => ?_⟩
    · have h1 : κ (g v) (z (g.symm (g v))) = (g v).embedding y := h (g v)
      rw [← hκ] at h1
      simpa using h1
    · change κ w (z (g.symm w)) = _
      rw [h, hκ]
  · rw [hcard]
    exact HasCov.of_measurePreserving _ hmp (fun _ => Iff.rfl) hcov

theorem exists_fund_ipow : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)), IsPlaces σ → ∀ (𝔡 : Ideal (𝓞 K)) (n : ℤ) (c : ι → ℂ), 𝔡 ≠ ⊥ → (∀ v, c v ≠ 0) → ∃ F : Set (ι → ℂ), MeasurableSet F ∧ (∀ a : ι → ℂ, ∃! t : K, t ∈ ipow 𝔡 n ∧ ((fun v => c v * σ v t) + a) ∈ F) ∧ volume F = ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ∏ v, ‖c v‖ ^ 2) := by
  intro K _ _ _ hK ι _ σ hσ 𝔡 n c h𝔡 hc
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔡
  obtain ⟨L₀, hL₀, hcov⟩ := exists_lat K hK.1 ι σ hσ.2 _ (zpow_ne_zero n h0)
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) :=
    LinearMap.pi fun v => (Algebra.lmul ℝ ℂ (c v)⁻¹).comp (LinearMap.proj v)
  have hf : ∀ z v, f z v = (c v)⁻¹ * z v := fun _ _ => rfl
  have hdet : LinearMap.det f = (∏ v, ‖c v‖ ^ 2)⁻¹ := by
    rw [LinearMap.det_pi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]
  have hpos : 0 < ∏ v, ‖c v‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hc v)) _
  let L : Submodule ℤ (ι → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ ∃ t ∈ ipow 𝔡 n, z = fun v => c v * σ v t := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => funext fun v => ?_, fun h v => ?_⟩
    · rw [← h, hf, mul_inv_cancel_left₀ (hc v)]
    · rw [hf, h, inv_mul_cancel_left₀ (hc v)]
  obtain ⟨v₀, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
  refine ⟨latticeDomain L, measurableSet_latticeDomain L, fun a => ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := existsUnique_add_mem_latticeDomain L a
    obtain ⟨t, ht, hzt⟩ := (hL z).1 z.2
    refine ⟨t, ⟨ht, by rw [← hzt, add_comm]; exact hz⟩, ?_⟩
    rintro t' ⟨ht', h'⟩
    have h1 := hu ⟨_, (hL _).2 ⟨t', ht', rfl⟩⟩ (by rw [add_comm] at h'; exact h')
    have h2 := congrFun ((congrArg Subtype.val h1).trans hzt) v₀
    exact (σ v₀).injective (mul_left_cancel₀ (hc v₀) h2)
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet, abs_of_pos (inv_pos.2 hpos),
      div_inv_eq_mul, map_zpow₀, FractionalIdeal.coeIdeal_absNorm] at h
    have hfin : volume (latticeDomain L) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]
    congr 1
    push_cast
    ring

end GlobalTheory.IdealFund
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LevelFamilies

theorem relIndex_eq_card_map {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M A : Submodule O V) :
    M.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A.map M.mkQ) := by
  have h := AddSubgroup.relIndex_ker A.toAddSubgroup M.mkQ.toAddMonoidHom
  have hk : M.mkQ.toAddMonoidHom.ker = M.toAddSubgroup := by
    ext x
    simp [AddMonoidHom.mem_ker]
  rw [hk] at h
  rw [h]
  rfl

theorem ncard_classes {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M B A : Submodule O V) (hMB : M ≤ B) (hBA : B ≤ A) [Finite (A.map M.mkQ)] :
    Set.ncard {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      Nat.card (A.map M.mkQ) - Nat.card (B.map M.mkQ) := by
  have hinj : Function.Injective (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) := by
    intro c c' h
    obtain ⟨v, rfl⟩ := M.mkQ_surjective c
    have : v ∈ (M.mkQ ⁻¹' {c'} : Set V) := by
      have h' : (M.mkQ ⁻¹' {M.mkQ v} : Set V) = M.mkQ ⁻¹' {c'} := h
      rw [← h']; simp
    simpa using this
  have hpre : ∀ y : V, (M.mkQ ⁻¹' {M.mkQ y} : Set V) = {x | x - y ∈ M} := by
    intro y
    ext x
    simp [Submodule.Quotient.eq]
  have hmem : ∀ y : V, M.mkQ y ∈ B.map M.mkQ ↔ y ∈ B := by
    intro y
    constructor
    · rintro ⟨b, hb, hby⟩
      have h1 : b - y ∈ M := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y = b - (b - y) := by abel
      rw [h2]
      exact B.sub_mem hb (hMB h1)
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hset : {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) ''
        ((A.map M.mkQ : Set (V ⧸ M)) \ (B.map M.mkQ : Set (V ⧸ M))) := by
    ext C
    constructor
    · rintro ⟨y, hyA, hyB, rfl⟩
      exact ⟨M.mkQ y, ⟨⟨y, hyA, rfl⟩, fun h => hyB ((hmem y).1 h)⟩, hpre y⟩
    · rintro ⟨c, ⟨⟨y, hyA, rfl⟩, hc⟩, rfl⟩
      exact ⟨y, hyA, fun h => hc ((hmem y).2 h), hpre y⟩
  have hsub : (B.map M.mkQ : Set (V ⧸ M)) ⊆ (A.map M.mkQ : Set (V ⧸ M)) :=
    Submodule.map_mono hBA
  have hfin : (A.map M.mkQ : Set (V ⧸ M)).Finite := Set.toFinite _
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_diff hsub (hfin.subset hsub)]
  rfl

theorem two_le_resQ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : 2 ≤ resQ ϖ := by
  have h : Ideal.span {ϖ} = IsLocalRing.maximalIdeal 𝒪[F] := hϖ.maximalIdeal_eq.symm
  have h1 : resQ ϖ = Nat.card (IsLocalRing.ResidueField 𝒪[F]) := by
    unfold resQ
    rw [h]
    rfl
  rw [h1]
  exact Finite.one_lt_card

theorem exists_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.TypeBe d Λ → ∃ i J i' : ℕ, 1 ≤ i ∧ (i : ℤ) ≤ S.a ∧ 1 ≤ J ∧ J ≤ r ∧ i' < i ∧ S.InFF (S.q ^ i) J (S.q ^ i - S.q ^ i') d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT hB
  obtain ⟨-, -, -, -, -, ⟨i, hia, hbe⟩, -, -, -, hlev0, hlev⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT
  have hMA : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hq : 2 ≤ S.q := two_le_resQ S.ϖ S.ϖ_irr
  have hcard : Nat.card ((S.sat Λ).map (S.M d Λ).mkQ) = S.q ^ i := by
    rw [← hbe, ← relIndex_eq_card_map]; rfl
  haveI hfin : Finite ((S.sat Λ).map (S.M d Λ).mkQ) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    positivity

  let P : ℕ → Prop := fun j => ∃ y ∈ S.sat Λ, S.levC d Λ y = j
  obtain ⟨y0, hy0A, hy0M⟩ : ∃ y ∈ S.sat Λ, y ∉ S.M d Λ := by
    by_contra h
    push_neg at h
    exact hB.1 (le_antisymm hMA h)
  let J := Nat.findGreatest P r
  have hle : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J := fun y hy =>
    Nat.le_findGreatest (hB.2.1 y hy) ⟨y, hy, rfl⟩
  have hPJ : P J := Nat.findGreatest_spec (hB.2.1 y0 hy0A) ⟨y0, hy0A, rfl⟩
  have hJr : J ≤ r := Nat.findGreatest_le r
  have hJ1 : 1 ≤ J := by
    have h1 : S.levC d Λ y0 ≠ 0 := fun h => hy0M ((hlev0 y0 hy0A).1 h)
    have := hle y0 hy0A
    omega

  let B : Submodule L.O S.V := S.sat Λ ⊓
    ((S.spanTo S.f (J - 1) ⊔ S.spanTo S.f' (J - 1)).restrictScalars L.O ⊔ S.M d Λ)
  have hBmem : ∀ y ∈ S.sat Λ, y ∈ B ↔ S.levC d Λ y ≤ J - 1 := by
    intro y hy
    rw [hlev y hy]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨u, hu, m, hm, rfl⟩ := Submodule.mem_sup.1 h
      exact ⟨u, hu, by simpa using hm⟩
    · rintro ⟨u, hu, hm⟩
      exact ⟨hy, Submodule.mem_sup.2 ⟨u, hu, y - u, hm, by abel⟩⟩
  have hMB : S.M d Λ ≤ B := le_inf hMA le_sup_right
  have hBA : B ≤ S.sat Λ := inf_le_left
  have hle' : B.map (S.M d Λ).mkQ ≤ (S.sat Λ).map (S.M d Λ).mkQ := Submodule.map_mono hBA
  haveI hfinB : Finite (B.map (S.M d Λ).mkQ) :=
    Finite.of_injective _ (Submodule.inclusion_injective hle')
  obtain ⟨i', hi'⟩ := (GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ S.ϖ_irr
    (B.map (S.M d Λ).mkQ)).1
  have hi'q : Nat.card (B.map (S.M d Λ).mkQ) = S.q ^ i' := hi'
  have hn : S.nLev d Λ J = S.q ^ i - S.q ^ i' := by
    rw [← hcard, ← hi'q, ← ncard_classes _ _ _ hMB hBA]
    unfold Frames.nLev
    congr 1
    ext C
    constructor
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, fun h => ?_, rfl⟩
      have := (hBmem y hy).1 h
      omega
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, ?_, rfl⟩
      have h1 := hle y hy
      have h2 : ¬ S.levC d Λ y ≤ J - 1 := fun h => hl ((hBmem y hy).2 h)
      omega
  have hlt : S.q ^ i' < S.q ^ i := by
    rw [← hcard, ← hi'q]
    obtain ⟨y, hy, hl⟩ := hPJ
    have hss : (B.map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) ⊂
        ((S.sat Λ).map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) := by
      refine ⟨hle', fun h => ?_⟩
      obtain ⟨b, hb, hby⟩ := h (⟨y, hy, rfl⟩ : (S.M d Λ).mkQ y ∈ (S.sat Λ).map (S.M d Λ).mkQ)
      have h1 : b - y ∈ S.M d Λ := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y ∈ B := by
        have h3 : y = b - (b - y) := by abel
        rw [h3]
        exact B.sub_mem hb (hMB h1)
      have := (hBmem y hy).1 h2
      omega
    exact Set.ncard_lt_ncard hss (Set.toFinite _)
  have hii : i' < i := (Nat.pow_lt_pow_iff_right (by omega)).1 hlt
  exact ⟨i, J, i', by omega, hia, hJ1, hJr, hii, hB, hbe, hle, hPJ, hn⟩

end GlobalTheory.HL.LevelFamilies
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFrameClasses_total_weight_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∃ d Λ, S.IsTerm d Λ) → (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  first | exact @GlobalTheory.HL.TotalWeight.sumCls_one_le | exact GlobalTheory.HL.TotalWeight.sumCls_one_le | (intros; apply GlobalTheory.HL.TotalWeight.sumCls_one_le <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.frameLattice_unimodular_generators_exponent_zero : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → ∃ u : Fin (2 * (r + 1)) → S.V, S.M d Λ = Submodule.span L.O (Set.range u) ∧ Submodule.span E (Set.range u) = S.ME ∧ (∀ i j, hf L S.Hm (u i) (u j) ∈ L.O) ∧ ∃ P : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) E, IsIntM L P ∧ (Matrix.of fun i j => hf L S.Hm (u i) (u j)) * P = 1 := by
  first | exact @GlobalTheory.HL.FrameUnimod.frame_unimodular | exact GlobalTheory.HL.FrameUnimod.frame_unimodular | (intros; apply GlobalTheory.HL.FrameUnimod.frame_unimodular <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.gluingImage_card_pow_le_defectGroup_card : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∃ i : ℕ, S.cardI d Λ = S.q ^ i) ∧ S.cardI d Λ ≤ S.be d Λ ∧ (¬ S.BBzero d Λ → ¬ S.TypeBe d Λ → S.q * S.cardI d Λ ≤ S.be d Λ) := by
  first | exact @GlobalTheory.HL.SmallImage.small_image | exact GlobalTheory.HL.SmallImage.small_image | (intros; apply GlobalTheory.HL.SmallImage.small_image <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev.DualIdeal

theorem smul_dual_iff {A V : Type} [CommRing A] [AddCommGroup V] [Module A V] (S : Subring A)
    (L : Submodule S V) (h : V → V → A) (hs : ∀ (a : A) x y, h x (a • y) = a * h x y)
    (hd : ∀ y, y ∈ L ↔ ∀ y' ∈ L, h y' y ∈ S) (t : S) (ht : IsUnit (t : A)) (y : V) :
    y ∈ (Ideal.span {t} : Ideal S) • L ↔ ∀ y' ∈ L, ∃ z ∈ (Ideal.span {t} : Ideal S), (z : A) = h y' y := by
  obtain ⟨u, hu⟩ := ht
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩ y' hy'
    refine ⟨t * ⟨_, (hd x).1 hx y' hy'⟩, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t), ?_⟩
    exact (hs t y' x).symm
  · intro H
    refine ⟨((u⁻¹ : Aˣ) : A) • y, (hd _).2 fun y' hy' => ?_, ?_⟩
    · obtain ⟨z, hz, e⟩ := H y' hy'
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      rw [hs, ← e, Subring.coe_mul, ← hu, mul_comm (w : A), Units.inv_mul_cancel_left]
      exact w.2
    · show (t : A) • _ = y
      rw [← hu, smul_smul, Units.mul_inv, one_smul]

theorem hAf_smul (I : AutInst) (a : I.E ⊗[I.F] Af I.F) (x y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I x (a • y) = a * hAf I x y := by
  unfold hAf Formalism.UG.hform
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

theorem mem_extId_smul_iff : ∀ (I : AutInst) (𝔞 : Ideal (𝓞 I.E)), 𝔞 ≠ ⊥ → ∀ y : Fin I.n → (I.E ⊗[I.F] Af I.F), y ∈ extId I 𝔞 • I.Lf ↔ ∀ y' ∈ I.Lf, ∃ z ∈ extId I 𝔞, (z : (I.E ⊗[I.F] Af I.F)) = hAf I y' y := by
  intro I 𝔞 h𝔞 y
  obtain ⟨⟨t, ht, e⟩, -⟩ := GlobalTheory.T.integralAdeleIdealOfIdeal_principal_and_inter I 𝔞 h𝔞
  rw [e]
  exact smul_dual_iff (IntAf I.F I.E) I.Lf (hAf I) (hAf_smul I) (GlobalTheory.T.adelicLattice_selfDual_hermitian I) t ht y

end GlobalTheory.RowLev.DualIdeal
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

theorem _root_.GlobalTheory.T.exists_mem_Kset_acts_as_GL_mod_splitPrime : ∀ (I : AutInst) (N p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)) (fr : PlFrame I N p w), I.n = N → p.Prime → Ideal.absNorm w.asIdeal = p → ¬ IsConj I w w → ∀ M : GL (Fin N) (ZMod p), ∃ x ∈ I.Kset, (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = (M : Matrix (Fin N) (Fin N) (ZMod p)) *ᵥ fr.c y) ∧ ∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ¬ IsConj I w u → ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I u.asIdeal • I.Lf := by
  first | exact @GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away | exact GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away | (intros; apply GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.ConvContRep

theorem continuous_conv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [FirstCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) (ψ f : G → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hf : AEStronglyMeasurable f μ) (hi : ∀ C, IsCompact C → IntegrableOn f C μ) :
    Continuous fun x => ∫ z, ψ (x⁻¹ * z) * f z ∂μ := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hc
  set L : Set G := (fun p : G × G => p.1 * p.2) '' (K ×ˢ tsupport ψ) with hLdef
  have hL : IsCompact L := (hK.prod hc.isCompact).image continuous_mul
  refine continuousAt_of_dominated
    (bound := fun z => C * L.indicator (fun z => ‖f z‖) z) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hψ.comp (continuous_const_mul x⁻¹)).aestronglyMeasurable).mul hf
  · filter_upwards [hKx] with x hx
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ L
    · rw [Set.indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    · have h0 : ψ (x⁻¹ * z) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hm => hz ?_
        exact ⟨(x, x⁻¹ * z), ⟨hx, hm⟩, mul_inv_cancel_left x z⟩
      simp [h0, Set.indicator_of_notMem hz]
  · exact (IntegrableOn.integrable_indicator (hi _ hL).norm hL.isClosed.measurableSet).const_mul C
  · refine Filter.Eventually.of_forall fun z => ?_
    have hz : Continuous fun x : G => ψ (x⁻¹ * z) * f z := by fun_prop
    exact hz.continuousAt

theorem conv_isContRep : ∀ (B : RowsAut) (ψ : B.I.GA → ℂ) (F : B.I.L2 B.μf B.fund), Continuous ψ → HasCompactSupport ψ → IsContRep B (∫ y, ψ y • B.R y F ∂(B.I.muA B.μf)) (fun x => ∫ z, ψ (x⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) := by
  intro B ψ F hψ hc
  obtain ⟨iT2, iLC, iSC, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have iK : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA
    infer_instance
  obtain ⟨hl, -, -, -, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have iL : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  obtain ⟨-, -, hiso, hcontR, hext⟩ := GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous B
  obtain ⟨hEinv, hEm⟩ := hext F
  unfold IsContRep
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_conv _ ψ _ hψ hc hEm fun C hC => ((GlobalTheory.T.invariantExtension_integrableOn_compact B C hC).choose_spec F).1
  · intro γ hγ x
    calc ∫ z, ψ ((γ * x)⁻¹ * z) * B.I.ext F z ∂B.I.muA B.μf
        = ∫ w, ψ ((γ * x)⁻¹ * (γ * w)) * B.I.ext F (γ * w) ∂B.I.muA B.μf :=
          (integral_mul_left_eq_self (fun z => ψ ((γ * x)⁻¹ * z) * B.I.ext F z) γ).symm
      _ = ∫ w, ψ (x⁻¹ * w) * B.I.ext F w ∂B.I.muA B.μf := by
          refine integral_congr_ae ?_
          filter_upwards [hEinv] with w hw
          rw [hw γ hγ, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  · have hint : Integrable (fun y => ψ y • B.R y F) (B.I.muA B.μf) :=
      (hψ.smul (hcontR F)).integrable_of_hasCompactSupport hc.smul_right
    have hK : AEStronglyMeasurable (fun p : B.I.GA × B.I.GA => B.I.ext F (p.1 * p.2))
        (((B.I.muA B.μf).restrict B.fund).prod (B.I.muA B.μf)) :=
      hEm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_mul ((B.I.muA B.μf).restrict B.fund) (B.I.muA B.μf))
    have hw := (GlobalTheory.ConvKernel.weak_integral_ae_eq (fun x g => B.I.ext F (x * g)) hK
      (fun g => B.R g F) (fun g => B.R_spec g F) ‖F‖ (fun g => (hiso g F).le) ψ
      (hψ.integrable_of_hasCompactSupport hc) (∫ y, ψ y • B.R y F ∂B.I.muA B.μf)
      (fun u => by rw [← integral_inner (𝕜 := ℂ) hint u]; simp only [inner_smul_right])).2
    filter_upwards [hw] with x hx
    refine hx.trans ?_
    rw [← integral_mul_left_eq_self (fun z => ψ (x⁻¹ * z) * B.I.ext F z) x]
    simp only [inv_mul_cancel_left]

end GlobalTheory.ConvContRep
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.haar_subgroup_bi_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∀ m ∈ NW ε W, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  first | exact @GlobalTheory.UnipUnimod.unimodular_NW | exact GlobalTheory.UnipUnimod.unimodular_NW | (intros; apply GlobalTheory.UnipUnimod.unimodular_NW <;> assumption)
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

theorem _root_.GlobalTheory.T.canonicalLatticeFiltration_size_properties : ∀ (I : AutInst) (x : I.GA) (t : ℝ), 0 < t → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLe I x t) ∧ IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLt I x t) ∧ stepLt I x t ≤ stepLe I x t ∧ (∀ t', t < t' → stepLe I x t ≤ stepLt I x t') ∧ (stepLe I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLe I x t) ≤ t) ∧ (stepLt I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLt I x t) < t) ∧ (∀ N, stepLe I x t < N → N ≤ lamX I x → t < sizeQ (bas I) (frm I x) N (stepLe I x t)) ∧ (∀ N, stepLt I x t < N → N ≤ lamX I x → t ≤ sizeQ (bas I) (frm I x) N (stepLt I x t)) ∧ (1 ≤ I.n → 0 < least I x ∧ (stepLe I x t = ⊥ ↔ t < least I x) ∧ (stepLt I x t = ⊥ ↔ t ≤ least I x)) := by
  first | exact @GlobalTheory.CountSteps.steps | exact GlobalTheory.CountSteps.steps | (intros; apply GlobalTheory.CountSteps.steps <;> assumption)
end
