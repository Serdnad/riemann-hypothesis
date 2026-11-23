module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle825
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle515
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle458
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle184
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle517
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle445
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct



theorem congLev_clauses : ∀ (D : D7) (c : GlobalTheory.EvenOnto.Com D) (s : GlobalTheory.EvenOnto.PiLocalization₂ D) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ c.S) → IsSelfDualC s.V s.Λ → s.J = Lev.levA s.V (congLev D.sp.cm s.V.gram s.Λ 𝔪) → s.J ≤ GfC s.V ∧ (∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧ ∀ k ∈ U, k ∈ GfC s.V → k ∈ s.J) ∧ (∀ k ∈ s.J, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ (∀ k ∈ GfC s.V, k ∈ GlobalTheory.EvenOnto.intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) → k ∈ s.J) ∧ SphOff (s.J : Set (GA D s.V)) 1 c.S ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ s.J, ∃ k₁ ∈ s.J, ∃ k₂ ∈ s.J, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  intro D c s 𝔪 h𝔪 hS hsd hJ
  have hΛ : Submodule.IsFullLattice D.host.E s.Λ :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice s.V s.Λ hsd
  obtain ⟨β, hβ⟩ := frame_exists_alt D.host.F D.host.E s.V.rank s.Λ hΛ
  have memJ : ∀ k, k ∈ s.J ↔ k ∈ GfC s.V ∧ Lev.finE s.V k ∈ congLev D.sp.cm s.V.gram s.Λ 𝔪 := by
    intro k; rw [hJ]; exact Iff.rfl
  have toSt : ∀ x, x ∈ congLev D.sp.cm s.V.gram s.Λ 𝔪 → x ∈ Formalism.L2.DIV.St β := fun x hx =>
    (GlobalTheory.LevSplit.mem_St_iff β s.Λ hβ x).2 (stab_of_mem_congLev hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; exact ((memJ k).1 hk).1
  · exact ⟨(congLev D.sp.cm s.V.gram s.Λ 𝔪).comap (Lev.finE s.V), (GlobalTheory.FunObj.congLev_open_compact s.V hΛ h𝔪).1,
      fun k hk hkf => (memJ k).2 ⟨hkf, hk⟩⟩
  · intro k hk v
    exact (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V β s.Λ hβ k).1 (toSt _ ((memJ k).1 hk).2) v
  · intro k hkf hint h1
    exact (memJ k).2 ⟨hkf, GlobalTheory.T.finitePoint_mem_congruenceSubgroup_offPlaces D s.V c.S 𝔪 h𝔪 hS k hkf hint h1⟩
  · intro P hP
    obtain ⟨T1, T2, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V
    obtain ⟨e, f, hi⟩ := T2 P
    refine ⟨e, f, hi, fun g hg => ?_, fun _ _ _ => rfl⟩
    obtain ⟨hff, hcf, -, -⟩ := T3 P e f hi
    obtain ⟨⟨Lf, hLf⟩, -, -⟩ := T1 f hff hcf
    obtain ⟨a, ha, u, hu⟩ := exists_idem_eq h𝔪 hS hP hi
    have hL0 : Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.LevSplit.L0sub s.V) = Formalism.L2.Herm.hatL (F := D.host.F) s.Λ := by
      congr 1; exact SetLike.coe_injective (GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice s.V)
    rw [GlobalTheory.LevSplit.ksph_iff, hL0, SetLike.mem_coe, memJ]
    constructor
    · rintro ⟨hG, hK⟩
      exact ⟨hG, stab_of_mem_congLev hK⟩
    · rintro ⟨hG, h1, h2⟩
      have s1 := GlobalTheory.LevSplit.supp_fin s.V hg
      have s2 := GlobalTheory.LevSplit.supp_fin s.V ((hLf _).1 (Lf.inv_mem ((hLf _).2 hg)))
      rw [MonoidHom.map_inv] at s2
      rw [← hu] at s1 s2
      refine ⟨hG, mem_congLev_of _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA s.V g) ?_ ?_⟩
      · exact cong_of_eq s.Λ ha u _ _ s1.symm h1
      · exact cong_of_eq s.Λ ha u _ _ s2.symm h2
  · intro P e f hP hi k hk
    obtain ⟨T1, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V
    obtain ⟨hff, hcf, hG, -⟩ := T3 P e f hi
    obtain ⟨⟨Lf, hLf⟩, hsplit, -⟩ := T1 f hff hcf
    obtain ⟨⟨Lf', hLf'⟩, -, -⟩ := T1 (1 - f) (by rw [mul_sub, mul_one, sub_mul, one_mul, hff, sub_self, sub_zero])
      (by rw [RingHom.map_sub, RingHom.map_one, hcf])
    obtain ⟨k₁, k₂, h1, h2, hk12⟩ := hsplit k
    obtain ⟨a, ha, u, hu⟩ := exists_idem_eq h𝔪 hS hP hi
    have hinv : SuppF s.V f k₁⁻¹ := (hLf _).1 (Lf.inv_mem ((hLf _).2 h1))
    have hinv' : SuppF s.V (1 - f) k₂⁻¹ := (hLf' _).1 (Lf'.inv_mem ((hLf' _).2 h2))
    have hφφ : GlobalTheory.LevSplit.finSw D f * GlobalTheory.LevSplit.finSw D f = GlobalTheory.LevSplit.finSw D f := by
      rw [← RingHom.map_mul, hff]
    rw [← hu] at hφφ
    have s1 := GlobalTheory.LevSplit.supp_fin s.V h1
    have s1' := GlobalTheory.LevSplit.supp_fin s.V hinv
    have s2 := GlobalTheory.LevSplit.supp_fin s.V h2
    have s2' := GlobalTheory.LevSplit.supp_fin s.V hinv'
    rw [MonoidHom.map_inv] at s1' s2'
    rw [RingHom.map_sub, RingHom.map_one] at s2 s2'
    rw [← hu] at s1 s1' s2 s2'
    obtain ⟨-, hkK⟩ := (memJ k).1 hk
    have hK' := stab_of_mem_congLev hkK
    have ek : Lev.finE s.V k = Lev.finE s.V k₁ * Lev.finE s.V k₂ := by rw [hk12, MonoidHom.map_mul]
    have m1 : k₁ ∈ s.J := by
      refine (memJ k₁).2 ⟨hG k₁ h1, mem_congLev_of _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA s.V k₁) ?_ ?_⟩
      · exact cong_of_eq s.Λ ha u _ _ (comp_sub_one _ hφφ _ _ _ s1 s2 (Or.inl (by rw [ek, Units.val_mul]))) hK'.1
      · exact cong_of_eq s.Λ ha u _ _
          (comp_sub_one _ hφφ _ _ _ s1' s2' (Or.inr (by rw [ek, _root_.mul_inv_rev, Units.val_mul]))) hK'.2
    refine ⟨k₁, m1, k₂, ?_, h1, h2, hk12⟩
    have : k₂ = k₁⁻¹ * k := by rw [hk12, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ m1) hk

end GlobalTheory.CongMember
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.HalfLatFrames

theorem halfLat_iff_isIntM : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x →
  (x ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) ↔ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he x hx
  have hR : GlobalTheory.Hk3.Core R F := hL.1
  have hPT : PrimeToHost R t := hL.2.1
  obtain ⟨cV, hcV⟩ := hR.lev.βV i
  obtain ⟨cW, hcW⟩ := hR.lev.βW i
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
  have hP : ∀ PP ∈ R.Pg ∪ R.Q t,
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hmem
    refine hPT PP (Finset.mem_union.1 hPP) ?_
    have : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
        ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) * (D.host.d : 𝓞 D.host.E) := by
      push_cast; ring
    rw [this]
    exact PP.asIdeal.mul_mem_right _ hmem
  constructor
  · intro hmem
    exact GlobalTheory.T.adjointFrameMatrix_integral_of_conjugate_half D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) sV sW hcV.1 hcW.1
      (R.Pg ∪ R.Q t) e he hP x hmem hx
  · intro hint
    exact GlobalTheory.T.idempotent_sum_self_dual_frames_bound D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) sV sW hcV.1 hcW.1
      (R.Pg ∪ R.Q t) e he hP x hx hint

end GlobalTheory.HalfLatFrames
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem exists_tprod_ne_zero_of_cc {D : D7} {c : Com D} {s : PiLocalization₂ D} (z : s.CC c) (hz : z ≠ 0) :
    ∃ v : s.M.Vec, PiTensorProduct.tprod ℂ v ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply hz
  apply Subtype.ext
  show (z : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0
  apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := ℂ) (s := fun τ => s.M.sm τ))
  rintro w ⟨v, rfl⟩
  simp [hne v]

theorem ip_unique {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD ipD' : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip ip' : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (h' : IsMet c s ipD' ip')
    (z : s.CC c) (hz : z ≠ 0) (x y : s.CC c) : ip x y = ip' x y := by
  obtain ⟨v, hv⟩ := exists_tprod_ne_zero_of_cc z hz
  have d : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) =
      ipD' (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) := by rw [h.pure, h'.pure]
  have dne : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    intro h0
    have := h.posD _ hv
    rw [h0] at this
    simp at this
  have e1 := h.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  have e2 := h'.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  rw [e1, ← d] at e2
  exact mul_right_cancel₀ dne e2

theorem reach_is {D : D7} {c : Com D} {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {k : ℕ} {s : PiLocalization₂ D} {Θ : s.CC c →ₗ[ℂ] s₀.CC c}
    (hR : Reach c s₀ k s Θ) : s.Is c k := by
  cases hR with
  | zero => exact hs₀
  | step _ hs' _ _ => exact hs'

theorem thetaChain_upward_induction_fixed_metric {D : D7} (hMet : MetEx D) (hSU : StepUp D) {c : Com D} (hc : c.Is)
    {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {ipD₀ ip₀} (h₀ : IsMet c s₀ ipD₀ ip₀) {u : s₀.CC c} {B : GlobalTheory.LFun.Fam D.host.E}
    (hu : IsPar u B) (hL : ∀ k < c.m, LNe c (c.χ k) (chainPar c B k)) {k : ℕ} {s : PiLocalization₂ D}
    {Θ : s.CC c →ₗ[ℂ] s₀.CC c} (hR : Reach c s₀ k s Θ) : k ≤ c.m → s.Is c k ∧
      ∀ ipD ip, IsMet c s ipD ip → ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k) := by
  induction hR with
  | zero =>
    intro _
    refine ⟨hs₀, fun ipD ip h => ⟨u, fun y => ?_, hu⟩⟩
    exact ip_unique h h₀ u hu.1 y u
  | @step k s Θ _ s' hs' p hp ih =>
    intro hk
    obtain ⟨hsk, ih⟩ := ih (by omega)
    refine ⟨hs', fun ipD' ip' h' => ?_⟩
    obtain ⟨ipD, ip, hm⟩ := hMet c hc k (by omega) s hsk
    obtain ⟨x, hx, hxp⟩ := ih ipD ip hm
    obtain ⟨x', hx', hx'p⟩ := hSU c hc k (by omega) s s' hsk hs' p hp ipD ip ipD' ip' hm h' x (chainPar c B k) hxp
      (hL k (by omega))
    refine ⟨x', fun y => ?_, ?_⟩
    · rw [hx', hx]
      rfl
    · rw [chainPar_succ]
      exact hx'p

theorem chainUp_of : ∀ D : D7, MetEx D → ParBound D → ChainL D → StepUp D → ChainUp D := by
  intro D hMet hPB hCL hSU c hc s₀ hs₀ k hk s Θ hR
  refine ⟨reach_is hs₀ hR, fun ipD₀ ip₀ ipD ip h₀ h u B hu => ?_⟩
  have hb := hPB c hc 0 (Nat.zero_le _) s₀ hs₀ u B hu
  have hr : s₀.V.rank = c.n := by rw [hs₀.rank]; simp
  rw [hr] at hb
  exact (thetaChain_upward_induction_fixed_metric hMet hSU hc hs₀ h₀ hu (fun k hk => hCL c hc B hb k hk) hR hk).2 ipD ip h

theorem ontoAll_of : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ParBound D → StepUp D → OntoAll D := by
  intro D hFin hMet hEig hInd hPB hSU c hc s₀ hs₀ k hk s Θ hR
  have hUp := chainUp_of D hMet hPB (GlobalTheory.T.evenThetaChain_LValues_ne_zero_and_params_injective D).1 hSU
  obtain ⟨hs, hadj⟩ := hUp c hc s₀ hs₀ k hk s Θ hR
  obtain ⟨ipD₀, ip₀, hm₀⟩ := hMet c hc 0 (Nat.zero_le _) s₀ hs₀
  obtain ⟨ipD, ip, hm⟩ := hMet c hc k hk s hs
  haveI : FiniteDimensional ℂ (s₀.CC c) := hFin c hc 0 (Nat.zero_le _) s₀ hs₀
  let Sab := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  let R : GlobalTheory.LFun.Fam D.host.E → GlobalTheory.LFun.Fam D.host.E → Prop := fun B B' => ∀ w ∉ Sab, B w = B' w
  have hRe : Equivalence R :=
    ⟨fun _ _ _ => rfl, fun h w hw => (h w hw).symm, fun h h' w hw => (h w hw).trans (h' w hw)⟩
  have hlin₀ := (GlobalTheory.T.multiplicity_vanishing_and_same_params_subspace D hMet).2 c s₀
  refine GlobalTheory.T.surjective_of_adjoint_separates_labelled_parts (s₀.CC c) (s.CC c) (GlobalTheory.LFun.Fam D.host.E) (GlobalTheory.LFun.Fam D.host.E) ip₀ ip Θ
    (fun u B => IsPar u B) (fun x B => IsPar x B) R R (fun B => chainPar c B k)
    hm₀.herm hm₀.pos hm.pos hRe (hEig c hc 0 (Nat.zero_le _) s₀ hs₀) hlin₀.1 hlin₀.2 ?_ ?_ ?_
  · intro B B' h w hw
    exact (GlobalTheory.T.evenThetaChain_LValues_ne_zero_and_params_injective D).2 c k B B' w (h w hw)
  · intro ι x B hx hne
    refine hInd c hc k hk s hs ι x B hx ?_
    intro i i' hii'
    have := hne i i' hii'
    by_contra hcon
    push_neg at hcon
    exact this hcon
  · intro u B hu
    exact hadj ipD₀ ip₀ ipD ip hm₀ hm u B hu

end GlobalTheory.EvenOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.ValPart

theorem lift_compMultilinearMap' {ι : Type*} [Fintype ι] {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module ℂ (Mi i)]
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (L : E →ₗ[ℂ] F) (T : MultilinearMap (RingHom.id ℂ) Mi E) :
    PiTensorProduct.lift (L.compMultilinearMap T) = L ∘ₗ PiTensorProduct.lift T := by
  apply PiTensorProduct.ext
  ext v
  simp

theorem valPart_mem : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → ForStage D fun c _ s => ∀ (u : s.CC c) w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e := by
  intro hCRD D hMet c hc j hj s hs u w B hw hB
  have hconjH := (GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hCRD D c hc j hj s hs).2
  have hBV : GlobalTheory.LFun.IsParamFunV s.V c.S (fun g => conj (PiLocalization₂.val u w g)) B := hB
  obtain ⟨a, ha⟩ := GlobalTheory.ParamEigen.eig_of_param D s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S
    hs.sph B
  have heig : ∀ P d R, Hecke₂ s.V (s.J : Set (GA D s.V)) 1 c.S P d R →
      heckeLin s.V R (PiLocalization₂.val u w) = conj (a P d) • PiLocalization₂.val u w := by
    intro P d R hR
    have h1 := ha _ hBV P d R hR
    rw [hconjH] at h1
    funext g
    have h2 := congrArg (starRingEnd ℂ) (congrFun h1 g)
    simpa [map_mul] using h2
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M s.J (1 : GA D s.V → ℂ) c.S
    GlobalTheory.ChainOntoSph.exists_unif_of_F hc.inf (fun _ _ _ _ => by simp) hs.split
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (by simp [PiLocalization₂.val])
  refine ⟨fun P d => conj (a P d), ?_⟩
  have hT : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      Mult c.θ s.M (s.J : Set (GA D s.V)) 1 :=
    (mem_multT c.θ s.M _ _ _).1 u.2
  rw [mem_partFull]
  refine ⟨hT, fun P d R hR v => ?_⟩
  obtain ⟨hkeep, -, -⟩ := hops.2.2 P d R hR
  set T := PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) with hTdef
  have hT' : heckeOn s.M R T - conj (a P d) • T ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) 1 :=
    Submodule.sub_mem _ (hkeep T hT) (Submodule.smul_mem _ _ hT)
  have hmem : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) ∈ s.CC c := by
    show _ ∈ MultT c.θ s.M _ _
    rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact hT'
  let x : s.CC c := ⟨_, hmem⟩
  have hlift : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) =
      heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) - conj (a P d) • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := by
    rw [map_sub, map_smul, heckeOn, postOn]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [lift_compMultilinearMap', hTdef, LinearEquiv.apply_symm_apply]
  have hx : PiLocalization₂.val x w = 0 := by
    show PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) w = 0
    rw [hlift]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [sub_eq_zero]
    exact heig P d R hR
  have hx0 := (GlobalTheory.T.multiplicity_vanishing_and_same_params_subspace D hMet).1 c hc j hj s hs x w hw0 hx
  have h3 : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) = 0 := congrArg Subtype.val hx0
  have h4 : heckeOn s.M R T - conj (a P d) • T = 0 := by
    have h := congrArg PiTensorProduct.lift.symm h3
    rwa [LinearEquiv.symm_apply_apply, map_zero] at h
  have h5 := congrArg (fun U : MMap s.M => U v) h4
  simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, MultilinearMap.zero_apply, sub_eq_zero] at h5
  simpa [heckeOn, postOn_apply] using h5

end GlobalTheory.EvenOnto.ValPart

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto.ZetaNeProof

variable {D : D7}

theorem coefW_mul_lev {c : Com D} {s s' : PiLocalization₂ D} (p : Step c s s') (m : Measure (WO s.V s'.V))
    (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (hlaw : ∀ κ ∈ s.J, (p.ω (κ, 1)) (p.pt φ) = p.pt φ)
    (b : GA D s.V) (κ : GA D s.V) (hκ : κ ∈ s.J) :
    coefW p.ω m X (p.pt φ) (b * κ) = coefW p.ω m X (p.pt φ) b := by
  have hmul : p.ω (b * κ, 1) = p.ω (b, 1) * p.ω (κ, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hv : p.ω (b * κ, 1) (p.pt φ) = p.ω (b, 1) (p.pt φ) := by
    rw [hmul, Module.End.mul_apply, hlaw κ hκ]
  unfold coefW
  rw [hv]

theorem hgtS_mul_lev {c : Com D} {s : PiLocalization₂ D} (hs : IsSelfDualC s.V s.Λ) (hfin : s.J ≤ GfC s.V)
    (hstab : ∀ k ∈ s.J, ∀ v,
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v)
    (a : GL (Fin s.V.rank) (AE D)) (b : GinfC s.V) (κ : GA D s.V) (hκ : κ ∈ s.J) :
    hgtS c s a ((b : GA D s.V) * κ) =
      ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.doublingHeight_eq_one_lattice_stabilizer_components D s.V s.Λ hs
  have hκf : κ ∈ GfC s.V := hfin hκ
  unfold hgtS
  have hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) =
      GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V) := by
    intro w
    rw [map_mul, h2 κ hκf w, mul_one]
  have hF : ∀ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v
      (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v ((b : GA D s.V) * κ)) = 1 := by
    intro v _
    rw [map_mul, h3 b b.2 v, one_mul]
    exact h1 v _ (hstab κ hκ v)
  simp only [hA]
  rw [Finset.prod_eq_one hF, mul_one]

theorem zetaNe_of_real : ∀ D : D7, MetEx D → RealZeta D → ZetaNe D := by
  intro D hMet hRZ
  intro c hc k hk s s' hs hs' p hp m X hcov
  obtain ⟨φ, v, hvK, hR⟩ := hRZ c hc k hk s s' hs hs' p hp m X hcov
  have hkm : k ≤ c.m := hk.le
  obtain ⟨ipD, ip, hip⟩ := hMet c hc k hkm s hs
  obtain ⟨⟨hmOff, _, hAsub, mR, hmR, hint⟩, hpet⟩ := GlobalTheory.T.evenThetaChainStage_levelMeasure_peterssonCoefficient D c hc k hkm s hs
  have hlaw : ∀ κ ∈ s.J, (p.ω (κ, 1)) (p.pt φ) = p.pt φ :=
    fun κ hκ => hp.pre.law φ κ hκ 1 s'.J.one_mem
  have hsupp := hp.pre.supp m X hcov φ
  obtain ⟨hz, hzI⟩ := hR mR hmR
  refine ⟨φ, PiTensorProduct.tprod ℂ v, Submodule.subset_span ⟨v, hvK, rfl⟩, ?_⟩
  intro u hu
  have hipu : ip u u ≠ 0 := by
    intro h0
    have := hip.pos u hu
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hcipu : conj (ip u u) ≠ 0 := (map_ne_zero _).mpr hipu

  have hlawZ : ∀ (b : GinfC s.V), ∀ κ ∈ s.J,
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) ((b : GA D s.V) * κ) =
        conj (ip u u) * (coefW p.ω m X (p.pt φ) (b : GA D s.V) *
          conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) := by
    intro b κ hκ
    unfold Step.zint
    rw [coefW_mul_lev p m X φ hlaw _ κ hκ, hpet ipD ip hip u v b κ hκ]
    simp only [map_mul]
    ring

  have hoff : ∀ g ∈ intOff c s \ s.big,
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) g = 0 := by
    rintro g ⟨hg, hgA⟩
    unfold Step.zint
    have h0 : coefW p.ω m X (p.pt φ) g = 0 := hsupp g hg hgA
    rw [h0, zero_mul]
  have hzInt : Integrable (fun g : GinfC s.V => coefW p.ω m X (p.pt φ) (g : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) mR := by
    by_contra hni
    exact hz (integral_undef hni)
  refine ⟨?_, ?_⟩
  · rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hmOff hAsub hoff]
    rw [(hint _ _ (hzInt.const_mul (conj (ip u u))) hlawZ).2, integral_const_mul]
    exact mul_ne_zero hcipu hz
  · intro a hmaj hcomp
    obtain ⟨s₁, hs₁, hI⟩ := hzI a hmaj hcomp
    refine ⟨s₁, hs₁, ?_⟩
    refine IntegrableOn.of_forall_diff_eq_zero (s := s.big) ?_ hmOff ?_
    · refine (hint _ _ (hI.const_mul (conj (ip u u))) ?_).1
      intro b κ hκ
      rw [hlawZ b κ hκ, hgtS_mul_lev hs.selfDual hs.fin hs.stab a b κ hκ, mul_assoc]
    · intro g hg
      rw [hoff g hg, zero_mul]

end GlobalTheory.EvenOnto.ZetaNeProof
end
