module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle482
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle537
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle629
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle630
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Formalism.UnipotentAdelicQuotients.SWXSDefs

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic Matrix
open scoped ValuativeRel
open PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSBound

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem psiOK_of_hasConductor {ψ₁ : AddChar F Circle} (h : GlobalTheory.SplitWeil.HasConductor ψ₁ 1) :
    PsiOK (Circle.coeHom.compAddChar ψ₁) := by
  have h1 : ∀ y : F, ValuativeRel.valuation F y ≤ 1 → ψ₁ y = 1 := fun y hy =>
    (h 1).mpr (by simp) y (by simpa using hy)
  refine ⟨fun x hx => ?_, ?_, fun x => Circle.norm_coe (ψ₁ x)⟩
  · simp [h1 x ((Valuation.mem_integer_iff _ _).mp hx)]
  · have hlt := GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one F
    have hne := GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_ne_zero F
    set ϖ : F := (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) with hϖdef
    have hϖ : ϖ ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
    have hinv : ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hϖ, map_one]
    have hnot : ¬ ValuativeRel.valuation F ϖ⁻¹ ≤ ValuativeRel.valuation F ((1 : Fˣ) : F) := by
      rw [Units.val_one, map_one]
      intro hle
      have h3 : ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ ≤
          ValuativeRel.valuation F ϖ * 1 := by gcongr
      rw [hinv, mul_one] at h3
      exact absurd hlt (not_lt.mpr h3)
    have hex : ¬ ∀ y : F, ValuativeRel.valuation F y ≤ ValuativeRel.valuation F ϖ⁻¹ → ψ₁ y = 1 :=
      fun hall => hnot ((h _).mp hall)
    push Not at hex
    obtain ⟨y, hy, hy1⟩ := hex
    refine ⟨y, ?_, ?_⟩
    · rw [Valuation.mem_integer_iff, map_mul]
      calc ValuativeRel.valuation F ϖ * ValuativeRel.valuation F y
          ≤ ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ := by gcongr
        _ = 1 := hinv
    · intro hc
      apply hy1
      apply Circle.ext
      rw [Circle.coe_one]
      exact hc

theorem mem_unipB_of_mem_unipotent {n : ℕ} {g : GL (Fin n) F} (hg : g ∈ Iwasawa.unipotent F n) :
    g ∈ GlobalTheory.SmGL.unipB F (Fin n) := by
  obtain ⟨hut, hdiag⟩ := hg
  have hp : g ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.points (Fin n)) := by
    intro i j hij
    exact hut (by simpa [GlobalTheory.SmGL.blk, GlobalTheory.SmGL.points] using hij)
  refine ⟨⟨g, hp⟩, ?_, rfl⟩
  show GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.points (Fin n)) ⟨g, hp⟩ = 1
  refine funext fun a => ?_
  show (GlobalTheory.SmGL.diagBlock F (GlobalTheory.SmGL.points (Fin n)) a).toHomUnits ⟨g, hp⟩ = 1
  apply Units.ext
  ext i j
  show (GlobalTheory.SmGL.diagBlock F (GlobalTheory.SmGL.points (Fin n)) a ⟨g, hp⟩) i j = (1 : Matrix Unit Unit F) i j
  obtain rfl : i = j := Subsingleton.elim _ _
  rw [Matrix.one_apply_eq]
  exact hdiag a

theorem superDiag_eq_superdiagSum {n : ℕ} (g : GL (Fin n) F) :
    GlobalTheory.Whittaker.superDiag g = Whittaker.superdiagSum (g : Matrix (Fin n) (Fin n) F) := by
  simp only [GlobalTheory.Whittaker.superDiag, GroundTheory.Automorphic.Whittaker.superdiagSum, Finset.sum_filter]

theorem whit_of_isFunctional {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} {ψ₁ : AddChar F Circle} {l : Module.Dual ℂ V}
    (h : GlobalTheory.Whittaker.IsFunctional ψ₁ ρ l) : Whit ρ (Circle.coeHom.compAddChar ψ₁) l := by
  intro g hg u
  rw [h g (mem_unipB_of_mem_unipotent hg) u, GroundTheory.Automorphic.Whittaker.psiN,
    ← superDiag_eq_superdiagSum]
  all_goals rfl

end Local

private theorem continuous_of_hasConductor_one {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ψ₁ : AddChar k Circle}
    (h : GlobalTheory.SplitWeil.HasConductor ψ₁ 1) : Continuous ψ₁ := by
  have h1 : ∀ y : k, ValuativeRel.valuation k y ≤ 1 → ψ₁ y = 1 := fun y hy =>
    (h 1).mpr (by simp) y (by simpa using hy)
  have hopen : IsOpen ((ValuativeRel.valuation k).integer : Set k) := Valuation.isOpen_integer
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' ((ValuativeRel.valuation k).integer : Set k),
    hopen.preimage (continuous_sub_right x), ?_, ?_⟩
  · show x - x ∈ (ValuativeRel.valuation k).integer
    rw [sub_self]
    exact zero_mem _
  · intro y hy
    have hy' : ψ₁ (y - x) = 1 := h1 _ ((Valuation.mem_integer_iff _ _).mp hy)
    calc ψ₁ y = ψ₁ ((y - x) + x) := by rw [sub_add_cancel]
      _ = ψ₁ (y - x) * ψ₁ x := AddChar.map_add_eq_mul _ _ _
      _ = ψ₁ x := by rw [hy', one_mul]

theorem global_character_holds : G4 := by
  intro E _ _ _ a ha π w
  obtain ⟨ψ₁, hψ⟩ := GlobalTheory.SplitWeil.Model.exists_hasConductor (k := w.adicCompletion E)
  have hne : ψ₁ ≠ 1 := by
    rintro rfl
    exact GlobalTheory.SplitWeil.Model.not_hasConductor_one 1 hψ
  obtain ⟨l, hl0, hl⟩ := GlobalTheory.Published.cuspidalGeneric_holds E a ha π w ψ₁
    (continuous_of_hasConductor_one hψ) hne
  exact ⟨_, psiOK_of_hasConductor hψ, l, hl0, whit_of_isFunctional hl⟩

end GlobalTheory.CompanionTheory.JSBound
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem length_decWord (Γ : Segment k) : (decWord Γ).length = Γ.len := by
  simp [decWord]

theorem decWord_get (Γ : Segment k) (a : Fin (decWord Γ).length) :
    (decWord Γ).get a = Γ.first.nu ((Γ.len - 1 - (a : ℕ) : ℕ) : ℂ) := by
  have h : (a : ℕ) < (List.ofFn Γ.term).reverse.length := a.2
  show (List.ofFn Γ.term).reverse[(a : ℕ)] = _
  rw [List.getElem_reverse, List.getElem_ofFn]
  simp [Segment.term]

theorem isCusp_decWord_get (Γ : Segment k) (a : Fin (decWord Γ).length) : ((decWord Γ).get a).IsCusp := by
  rw [decWord_get]
  exact Γ.isCusp_first.nu _

theorem sum_decWord (Γ : Segment k) : ∑ a, ((decWord Γ).get a).1 = Γ.deg := by
  have h : ∀ a, ((decWord Γ).get a).1 = Γ.d := fun a => by rw [decWord_get]; rfl
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, length_decWord]
  rfl

theorem below_of_len_one {s : ℕ} (Γ : Fin s → Segment k) (h : ∀ a, (Γ a).len = 1) (a : Fin s) :
    below Γ a = s - 1 - (a : ℕ) := by
  simp only [below, h, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]

theorem jmL_decWord (hJ : LSegJacquet k) (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hΓ : IsLSeg Γ π) : jmL (decWord Γ) π = 1 := by
  have hd : ∑ a, ((decWord Γ).get a).1 = N := (sum_decWord Γ).trans hΓ.deg_eq
  rw [jmL, dite_eq_left hd]
  refine (hJ Γ π hΓ _ (decWord Γ).get hd fun a => (isCusp_decWord_get Γ a).1).1
    ⟨fun a => Segment.single _ (isCusp_decWord_get Γ a), ⟨?_, fun a => ?_⟩,
      fun a => (single_spec (isCusp_decWord_get Γ a)).2.1⟩
  · have h : ∀ a, (Segment.single _ (isCusp_decWord_get Γ a)).len = 1 := fun _ => rfl
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, length_decWord]
  · refine (decWord_get Γ a).trans ?_
    have e : (decWord Γ).length - 1 - (a : ℕ) = Γ.len - 1 - (a : ℕ) := by
      have := length_decWord Γ
      omega
    rw [below_of_len_one _ (fun _ => rfl), e]

theorem len_eq_one (hJ : LSegJacquet k) {Δ : Segment k} {x : IrrGL (k := k)} (hx : x.IsCusp) (h : IsLSeg Δ x.rep) :
    Δ.len = 1 := by
  have hd : ∑ a, ((decWord Δ).get a).1 = x.1 := (sum_decWord Δ).trans h.deg_eq
  have h1 := jmL_decWord hJ Δ h
  rw [jmL, dite_eq_left hd, jm] at h1
  have hsub : IsSubquotient (piTensor fun a => ((decWord Δ).get a).rep)
      (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun a => ((decWord Δ).get a).1) hd) x.rep) :=
    jhMult_ne_zero_iff.1 (by rw [h1]; exact one_ne_zero)
  have hu := GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal k x.1 _ x.rep _ _ _ _
    (fun a => ((decWord Δ).get a).rep) hx.2 (fun a => nontrivial_of_irreducible ((decWord Δ).get a).2.rep.irr) hsub
  by_contra hne
  have hl : 2 ≤ (decWord Δ).length := by
    have := Δ.len_pos
    rw [length_decWord]
    omega
  have := hu ⟨0, by omega⟩ ⟨1, by omega⟩ (isCusp_decWord_get Δ _).1 (isCusp_decWord_get Δ _).1
  simp at this

theorem eq_of_isLSeg_single {ρ : IrrGL (k := k)} (hρ : ρ.IsCusp) {x : IrrGL (k := k)} (h : IsLSeg (.single ρ hρ) x.rep) : x = ρ := by
  have hdeg : ρ.1 = x.1 := by
    have := h.deg_eq
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨n, c⟩ := x
  obtain ⟨m, r⟩ := ρ
  obtain rfl : m = n := hdeg
  obtain ⟨φ⟩ := (single_spec hρ).2.1.unique h
  exact (IrrGL.of_rep _).symm.trans ((IrrGL.of_eq_of.2 ⟨φ⟩).trans (IrrGL.of_rep _))

theorem eq_first_of_len_one {Δ : Segment k} (hl : Δ.len = 1) {x : IrrGL (k := k)} (h : IsLSeg Δ x.rep) : x = Δ.first := by
  have e : Δ = .single Δ.first Δ.isCusp_first := Segment.ext_first rfl hl
  exact eq_of_isLSeg_single Δ.isCusp_first (e ▸ h)

theorem jmL_cusp_word : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsLSeg Γ π → ∀ W : List (IrrGL (k := k)), (∀ w ∈ W, w.IsCusp) →
    (W = decWord Γ → jmL W π = 1) ∧ (W ≠ decWord Γ → jmL W π = 0) := by
  intro k _ _ _ _ _ hJ Γ N V _ _ π hΓ W hW
  refine ⟨fun e => e ▸ jmL_decWord hJ Γ hΓ, fun hne => ?_⟩
  by_cases hd : ∑ a, (W.get a).1 = N
  · rw [jmL, dite_eq_left hd]
    refine (hJ Γ π hΓ _ W.get hd fun a => (hW _ (List.get_mem W a)).1).2 ?_
    rintro ⟨Γ', ⟨hs, hf⟩, hL⟩
    have hl : ∀ a, (Γ' a).len = 1 := fun a => len_eq_one hJ (hW _ (List.get_mem W a)) (hL a)
    have hlen : W.length = Γ.len := by
      simpa only [hl, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hs
    refine hne (List.ext_get (hlen.trans (length_decWord Γ).symm) fun n h1 h2 => ?_)
    have h3 : W.get ⟨n, h1⟩ = Γ.first.nu ((W.length - 1 - n : ℕ) : ℂ) := by
      have h4 := eq_first_of_len_one (hl ⟨n, h1⟩) (hL ⟨n, h1⟩)
      rw [hf, below_of_len_one Γ' hl] at h4
      exact h4
    rw [h3, decWord_get, hlen]
  · rw [jmL, dite_eq_right hd]

end GlobalTheory.CompanionTheory.FineL

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.FA
open scoped Classical

attribute [local instance] borelG borelF borelH

namespace GlobalTheory.CompanionTheory.FmPowP

section Generic

variable {H : Type} [Group H]

theorem hint_ind_left (K U : Subgroup H) (hUK : U ≤ K) (hi : U.relIndex K ≠ 0) (f : H → ℂ)
    (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) (m : H) :
    hint K (fun z => (U : Set H).indicator (fun _ => ((U.relIndex K : ℕ) : ℂ)) z * f (z⁻¹ * m)) = f m := by
  have hC : ((U.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hi
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K U _ hUK (fun k hk x => ?_) hi]
  · rw [finsum_eq_single _ ((1 : H) : H ⧸ U)]
    · have hmem : (((1 : H) : H ⧸ U).out : H) ∈ U := by
        have := QuotientGroup.out_eq' ((1 : H) : H ⧸ U)
        simpa using (QuotientGroup.eq.1 this)
      rw [Set.indicator_of_mem (by exact hmem), hl _ (inv_mem hmem)]
      field_simp
    · intro q hq
      have hnot : (q.out : H) ∉ U := fun h => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using inv_mem h))
      rw [Set.indicator_of_notMem (by exact hnot), zero_mul]
  · have h1 : (x * k ∈ (U : Set H)) ↔ x ∈ (U : Set H) := Subgroup.mul_mem_cancel_right U hk
    have h2 : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    rw [h2, hl _ (inv_mem hk)]
    by_cases hx : x ∈ (U : Set H)
    · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem hint_ind_right (K U : Subgroup H) (hUK : U ≤ K) (hi : U.relIndex K ≠ 0) (f : H → ℂ)
    (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) (m : H) :
    hint K (fun z => f z * (U : Set H).indicator (fun _ => ((U.relIndex K : ℕ) : ℂ)) (z⁻¹ * m)) = f m := by
  have hC : ((U.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hi
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K U _ hUK (fun k hk x => ?_) hi]
  · rw [finsum_eq_single _ ((m : H) : H ⧸ U)]
    · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U m
      have hmem : ((((m : H) : H ⧸ U).out : H))⁻¹ * m ∈ U := by
        rw [hu]; simp
      rw [Set.indicator_of_mem (by exact hmem), hu, hr _ u.2]
      field_simp
    · intro q hq
      have hnot : ((q.out : H))⁻¹ * m ∉ U := fun h => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 h)
      rw [Set.indicator_of_notMem (by exact hnot), mul_zero]
  · have h2 : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    have h1 : (k⁻¹ * (x⁻¹ * m) ∈ (U : Set H)) ↔ x⁻¹ * m ∈ (U : Set H) :=
      Subgroup.mul_mem_cancel_left U (inv_mem hk)
    rw [hr _ hk, h2]
    by_cases hx : x⁻¹ * m ∈ (U : Set H)
    · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem relIndex_ne_of_open [TopologicalSpace H] [IsTopologicalGroup H] {K U : Subgroup H}
    (hU : IsOpen (U : Set H)) (hK : IsCompact (K : Set H)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := hU.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem isCompact_maximal_pair_place (w : Pl E) : IsCompact ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  have h1 := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have h2 := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  simpa [Subgroup.coe_prod] using h1.prod h2

theorem mconv_idem_left {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) (f : LF a b w) (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) :
    PositivityTheory.Rg.BcN.F2.mconv (idem U) f = f := by
  funext m
  exact hint_ind_left _ U hUK (relIndex_ne_of_open hU (isCompact_maximal_pair_place w)) f hl m

theorem mconv_idem_right {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) (f : LF a b w) (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) :
    PositivityTheory.Rg.BcN.F2.mconv f (idem U) = f := by
  funext m
  exact hint_ind_right _ U hUK (relIndex_ne_of_open hU (isCompact_maximal_pair_place w)) f hr m

theorem mconv_zero_left {w : Pl E} (f : LF a b w) : PositivityTheory.Rg.BcN.F2.mconv (0 : LF a b w) f = 0 := by
  funext m
  simpa [PositivityTheory.Rg.BcN.F2.mconv] using GlobalTheory.CompanionTheory.FamClP.hint_zero (K2 a b w)

theorem mconv_zero_right {w : Pl E} (f : LF a b w) : PositivityTheory.Rg.BcN.F2.mconv f (0 : LF a b w) = 0 := by
  funext m
  simpa [PositivityTheory.Rg.BcN.F2.mconv] using GlobalTheory.CompanionTheory.FamClP.hint_zero (K2 a b w)

theorem idem_left {w : Pl E} (U : Subgroup (GLw a w × GLw b w)) (u) (hu : u ∈ U) (g) : idem U (u * g) = idem U g := by
  have h1 : (u * g ∈ (U : Set (GLw a w × GLw b w))) ↔ g ∈ (U : Set (GLw a w × GLw b w)) :=
    Subgroup.mul_mem_cancel_left U hu
  unfold idem
  by_cases hx : g ∈ (U : Set (GLw a w × GLw b w))
  · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

section Sel

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

end Sel

section Alg

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

theorem mconv_idem_idem {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) : PositivityTheory.Rg.BcN.F2.mconv (idem U) (idem U) = idem U :=
  mconv_idem_left hU hUK _ (idem_left U)

end Alg

section Lev

end Lev

section Act

end Act

section Main

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)] {S : Set (Pl E)} {P : Finset (Pl E)} {B : Block E}
  {e : B.κ ≃ ∀ w : P, κ w} {U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)} {L : LM κ B.a B.b}

variable (hAlg : FmAlg) (hAt : FmAtP) (hCM : Tail.ConvMul) (hAct : ActAlg) (hId : ActIdem) (hS : IsSection S)
  (hP : (↑P : Set (Pl E)) ⊆ S) (hU₁ : IsLev U₁) (hU₂ : IsLev U₂) (hok : L.Ok P) (hs : ∀ w, L.s w = idem (U₁ w))
  (ht : ∀ w, L.t w = idem (U₂ w))
  (hinv : ∀ w ∈ P, ∀ x y, ∀ u ∈ U₁ w, ∀ g, L.m w x y (u * g) = L.m w x y g ∧ L.m w x y (g * u) = L.m w x y g)









end Main

end GlobalTheory.CompanionTheory.FmPowP

end
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.block_triangular_mem_minimal_parabolic_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} (v : HeightOneSpectrum (𝓞 F)) (p : GLoc σ J v) (B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E)), B.BlockTriangular id → (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B → emb σ J v p ∈ minPar σ J X := by
  first | exact @GlobalTheory.CompanionTheory.KFin.emb_mem_minPar | exact GlobalTheory.CompanionTheory.KFin.emb_mem_minPar | (intros; apply GlobalTheory.CompanionTheory.KFin.emb_mem_minPar <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem _root_.GlobalTheory.T.iSup_finite_product_tail_limit : ∀ (ι : Type) [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι), Summable (fun v => |Mv v - 1|) → Summable (fun v => |τ v - 1|) → Summable (fun v => |p v - 1|) → (∀ v, 0 ≤ Mv v) → (∀ v, 0 ≤ τ v) → (∀ v, 0 ≤ p v) → (∀ v, v ∉ S → τ v * p v ≤ Mv v) → ⨆ S' : Finset ι, ENNReal.ofReal ((∏ v ∈ (S ∪ S') \ S, Mv v) * ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) = ENNReal.ofReal (∏' v : {v // v ∉ S}, Mv v.1) := by
  first | exact @GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails | exact GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails | (intros; apply GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails <;> assumption)
end
