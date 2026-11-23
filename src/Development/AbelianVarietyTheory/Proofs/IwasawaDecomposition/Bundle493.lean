module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle341
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle420
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle348
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle483
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle366
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle440
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle448
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle430
import Formalism.SharpRestriction.InertJacobiLevels.ExtraVal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle484
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle464
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle465
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle369
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCoefficientCompatibility
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw



theorem match_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))) (i : ℕ), i ≤ B.R.m → ∀ (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∃ (g : Chart I u a i → Ch0) (k : Chart I u a i → GA B (B.R.N i)), AdmK I u a i k ∧ ∀ β, ∃ c, chartOf I u a i c = β ∧ ∃ c0, chOf0 c0 = g β ∧ ∀ x : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) x = 1) → (∀ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ → ∃ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr c0.1 κ0) ∧ (∀ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 → ∃ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ) := by
  intro B X I hI hP l u a Q i hi Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 h1 h2 hQ hR0
  obtain ⟨c0f, t, ht1, ht2, ht3, hM⟩ := GlobalTheory.T.match_tupleChart_memberChart I hI hP l u a Q i hi h1 h2 hQ
  refine ⟨fun β => chOf0 (c0f β), fun β => k0 (chOf0 (c0f β)) * t β,
    GlobalTheory.T.admissibleBasePoint_chart_mul_twist_alt I hI u a i Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 hR0 _ t ht1 ht2 ht3, ?_⟩
  intro β
  obtain ⟨c, hc, hs⟩ := hM β
  refine ⟨c, hc, c0f β, rfl, ?_⟩
  intro x hx
  have e : (k0 (chOf0 (c0f β)) * t β)⁻¹ * x * (k0 (chOf0 (c0f β)) * t β) =
      (t β)⁻¹ * ((k0 (chOf0 (c0f β)))⁻¹ * x * k0 (chOf0 (c0f β))) * t β := by group
  rw [e]
  refine hs _ fun v hv => ?_
  rw [map_mul, map_mul, hx v hv, mul_one, map_inv, inv_mul_cancel]



theorem charts_match : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (k : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k ∧ ∀ (K : ∀ β : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.Reads u a i (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k → ∀ β, (∀ κ : (K β).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → ∃ h' : κ.1 ∈ (K0 (g β)).lev.U, (K β).lev.chi κ = (K0 (g β)).lev.chi ⟨κ.1, h'⟩) ∧ ∀ κ' : (K0 (g β)).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ'.1 = 1) → κ'.1 ∈ (K β).lev.U := by
  intro B X I hI hP l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR0
  obtain ⟨k0, hk0⟩ := hR0
  obtain ⟨g, k, hk, hM⟩ := match_base I hI hP l u a Q i hi Ch0 chOf0 _ _ _ _ _ k0 h1 h2 hQ hk0
  refine ⟨g, k, hk, ?_⟩
  intro K hK β
  obtain ⟨c, hc, c0, hc0, hx⟩ := hM β
  subst hc
  have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have huni : ∀ {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (B.T u) (I.rec7 l Z).R.f bad) (x : GA B (B.R.N i)), x ∈ S.U → x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) := by
    intro bad S x hx
    have h := ((S.U_eq x).1 hx).1
    rw [hgram] at h
    exact h
  have hnQ0 : ∀ v, ¬ I.UnderQ I.mu0 v := by
    rintro v ⟨P, hP, -⟩
    rw [ColIn.twistPrimes_reference_tuple_eq_empty] at hP
    exact absurd hP (Finset.notMem_empty _)
  refine ⟨fun κ hκ => ?_, fun κ' hκ' => ?_⟩
  · obtain ⟨κ1, hl1⟩ := GlobalTheory.T.chartLevel_twistTrivial_localMove I hI l u a i hi _ _ _ _ _ _ k hK c κ.1 (huni _ κ.1 κ.2)
      (fun v hv => hκ v ((hQ v).2 hv)) κ.2
    obtain ⟨κ0, hl0, hchr⟩ := (hx κ.1 hκ).1 κ1 hl1
    obtain ⟨hm0, hc0'⟩ := reads_of_locMv I hI hk0 c0 κ.1 κ0 (by rw [hc0]; exact hl0)
    obtain ⟨hm, hcc⟩ := reads_of_locMv I hI hK c κ.1 κ1 hl1
    have key : ∀ β0 (e : chOf0 c0 = β0), ∃ h' : κ.1 ∈ (K0 β0).lev.U,
        (((K0 β0).lev.chi ⟨κ.1, h'⟩ : ℂˣ) : ℂ) = B.embLL (((I.stp u I.mu0 i).chr c0.1 κ0 : B.LLˣ) : B.LL) := by
      intro β0 e
      subst e
      exact ⟨hm0, hc0'⟩
    obtain ⟨h', e'⟩ := key _ hc0
    refine ⟨h', Units.ext ?_⟩
    rw [e', ← hchr]
    exact hcc
  · have hm0 : κ'.1 ∈ (K0 (chOf0 c0)).lev.U := by rw [hc0]; exact κ'.2
    obtain ⟨κ0, hl0⟩ := GlobalTheory.T.chartLevel_twistTrivial_localMove I hI l u I.mu0 i hi _ _ _ _ _ _ k0 hk0 c0 κ'.1 (huni _ κ'.1 hm0)
      (fun v hv => absurd hv (hnQ0 v)) hm0
    rw [hc0] at hl0
    obtain ⟨κ, hl⟩ := (hx κ'.1 hκ').2 κ0 hl0
    exact (reads_of_locMv I hI hK c κ'.1 κ hl).1

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar


open GlobalTheory.Mem.SymChar.Resid in
theorem resid_at_w : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k N → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymChar.argS X k) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtA D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) := by
  intro D X _h _hE hgw kv k hk N hN
  classical
  have hg : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := hgw kv
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  set w := D.naut.plGw kv.1 kv.2 with hwdef
  let S : AddSubgroup (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := (wInt X w).toAddSubgroup
  let mk := QuotientAddGroup.mk' S
  have hmk : ∀ a b, a - b ∈ wInt X w → mk a = mk b := fun a b hab =>
    (QuotientAddGroup.eq_iff_sub_mem).2 hab
  let f0 : ℤ →+ (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ S :=
    mk.comp (Int.castAddHom (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
  have hf0 : f0 (D.host.g kv.1 : ℤ) = 0 := by
    show mk ((((D.host.g kv.1 : ℕ) : ℤ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) = 0
    rw [Int.cast_natCast]
    exact (QuotientAddGroup.eq_zero_iff _).2 (natCast_g_mem X kv.1 hg)
  let φ : ZMod (D.host.g kv.1) →+ (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ S :=
    ZMod.lift (D.host.g kv.1) ⟨f0, hf0⟩
  have hφ : ∀ t : ZMod (D.host.g kv.1), φ t = mk ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    intro t
    conv_lhs => rw [← ZMod.natCast_zmod_val t, ← Int.cast_natCast]
    rw [ZMod.lift_coe]
    show mk _ = mk _
    congr 1
    simp
  suffices hs : mk (argS X k) = φ (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then
      ((wtA D.R.rS D.R.k (side X w) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) by
    unfold ModW
    rw [hφ] at hs
    exact (QuotientAddGroup.eq_iff_sub_mem).1 hs
  have hsum : φ (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then
      ((wtA D.R.rS D.R.k (side X w) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) =
      ∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then wtA D.R.rS D.R.k (side X w) i j • φ (N i j) else 0 := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [← zsmul_eq_mul, map_zsmul]
    · exact map_zero φ
  rw [hsum, GlobalTheory.T.symmetricFrame_weightedEdgeSum_reindex _ D.R.rS D.R.k D.R.r (rank_eq D) (side X w) (fun i j => φ (N i j))]
  unfold argS

  rw [map_add (f := _), map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [hφ]
    apply hmk
    have := dual_row X w hN (X.vectorsInLattice.1 a).2 (posE D a) (GlobalTheory.T.flagDualVector_pairing_symmetricFrame_mod_place D X w kv.1 hg a) (posN D a)
    rw [symVec_posN] at this
    exact this
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.1 + 1 < D.R.k
    · rw [dite_eq_left hi, dite_eq_left hi]
      by_cases hw : SymFrame.EwAt X w
      · have hs : side X w = true := by simp [side, hw]
        rw [if_pos hs, hφ]
        apply hmk
        have h1 := one_sub_ew_mem X kv.1 hg hw
        have := dual_row X w hN (X.vectorsInLattice.2.2 i).2 (posB D i) (GlobalTheory.T.unipotentDualVector_pairing_symmetricFrame_mod_place D X w kv.1 hg hw h1 i)
          (posB D ⟨i.1 + 1, hi⟩)
        rw [symVec_posB X w hw] at this
        have e1 : (posB D ⟨i.1 + 1, hi⟩) = ⟨D.R.rS + i.1 + 1, by have := rank_eq D; omega⟩ :=
          Fin.ext (by simp only [posB]; omega)
        rw [e1] at this
        exact this
      · have hs : side X w = false := by simp [side, hw]
        rw [if_neg (by simp [hs])]
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
        have hew := GlobalTheory.T.idempotent_mem_placeIdealSpan_of_ne_one D X kv hw
        have hbw : X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩ ∈ X.B.I.Lf :=
          Formalism.L2.SG.Pf.unitaryCongruence.K_mv X.B.I hk (X.vectorsInLattice.2.2 _).1
        have hint := Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.2.2 i).2 hbw
        have e : hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) =
            hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) * X.ew := by
          conv_lhs => rw [X.bwd_w i]
          rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_left, Formalism.L2.SG.Pf.unitaryCongruence.sigA_sigA, mul_comm]
        show hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) ∈ wInt X w
        rw [e]
        exact (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hew
    · rw [dite_eq_right hi, dite_eq_right hi, map_zero]

end GlobalTheory.Mem.SymChar
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2


noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

theorem formRho_one_apply {Xf : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 Xf.E))}
    (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG))) (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)
    (h : Λ.grp) (v : C.V) :
    Formalism.L2.Col.formRho C Λ ((1 : Formalism.L2.Col.UF Xf.E n), h) v = ((Λ.chr h : Xf.Kˣ) : Xf.K) • v := by
  show (((Λ.chr h : Xf.Kˣ) : Xf.K) • C.rho 1) v = _
  rw [map_one]
  rfl


theorem act_key (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U)
    (A k : GL (Fin X.B.R.nV) (EA X)) (P : PresL X I hX U Xg tr L cV i t)
    (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q)
    (h : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.nV) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
    (hh : h ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp)
    (hpt : ∀ x : Bridge.Gf (Vc X.toD7 i), ptS X I U i t A k (x * κ) =
      ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
        h * (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
        ptS X I U i t A k x)
    (hch : X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
      (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ))
    (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (x : Bridge.Gf (Vc X.toD7 i)) :
    P.coef (((Formalism.L2.Col.unipotentRightActionFormsV X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1) (redQ X I U L eG i t κ) φ :
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) :
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (ptL X I U i t A k x)) =
      (((envL X I hX U Xg tr L cV i t).lev.ch κ)⁻¹ : ℂˣ) •
        P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptL X I U i t A k (x * κ))) := by
  have h1 := φ.2 (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), ⟨h, hh⟩) :
      Formalism.L2.Col.FormG (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv)
      (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x)
  have h2 : (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptS X I U i t A k (x * κ)) =
      ((((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K)) •
        (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x) := by
    rw [hpt x, ← one_mul (1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), ← Prod.mk_mul_mk, mul_smul]
    exact h1.trans (formRho_one_apply _ _ _ _)
  refine Eq.trans (congrArg P.coef (Formalism.L2.Col.trRep_apply _ _ _ _ _ φ _)) ?_
  have h3 : P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptS X I U i t A k (x * κ))) =
      (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) •
        P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x)) := by
    rw [h2]
    refine (P.coef.map_smulₛₗ _ _).trans ?_
    rw [hch]
  exact (inv_smul_smul ((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ) _).symm.trans (congrArg _ h3.symm)

theorem lemT : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
      ∃ h : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.nV) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1),
        ∃ hh : h ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
          (∀ x : Bridge.Gf (Vc X.toD7 i), LiftBrg.ActQ.ptS X I U i t A k (x * κ) =
            ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
              h * (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (LiftBrg.ActQ.redQ X I U L eG i t κ))⁻¹) •
              LiftBrg.ActQ.ptS X I U i t A k x) ∧
          X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
            (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) := by
  intro X px I U L eG hI hV hL hG i t A k hA κ
  obtain ⟨hh, hc⟩ := GlobalTheory.T.flagLift_translation_mem_typeLevel_character X px I U L eG hI hV hL hG i t A k hA κ
  refine ⟨_, hh, fun x => ?_, hc⟩
  rw [GlobalTheory.T.stdDecoratedLattice_rightTranslate_levelQ X px I U L hI hV hL i t A k hA κ x, mul_inv_cancel_right]


theorem lemAct : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    ∀ (g : Gc X.B px) (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q), LiftBrg.ActQ.redQ X I U L eG i t κ = g →
      ∀ f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms,
        P.ext ((((famR X I hX U Xg tr).A.leftGroupActionLift i t g f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms)) : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V) =
          Bridge.g0Act (LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch κ (P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP g κ hκ f
  obtain ⟨h, hh, hpt, hch⟩ := lemT X px I U L eG hI hV hL hG i t A k hA κ
  subst hκ
  funext x
  have e1 := hP ((famR X I hX U Xg tr).A.leftGroupActionLift i t (redQ X I U L eG i t κ) f) x
  have e2 := hP f (x * κ)
  unfold Bridge.g0Act
  refine e1.trans ?_
  refine Eq.trans ?_ (congrArg (fun w => (((LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch κ)⁻¹ : ℂˣ) • w) e2).symm
  have e3 : (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm
      ((famR X I hX U Xg tr).A.leftGroupActionLift i t (redQ X I U L eG i t κ) f)) =
      Formalism.L2.Col.unipotentRightActionFormsV X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1) (redQ X I U L eG i t κ)
        (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm f) :=
    LinearEquiv.symm_apply_apply _ _
  rw [e3]
  exact act_key X I hX U Xg tr L eG cV i t A k P κ h hh hpt hch _ x

theorem exists_actTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    ∃ a : Bridge.ActTie (Bridge.ratF (Vc X.toD7 i)) P (LiftBrg.envL X I hX U Xg tr L cV i t).lev.Q
        (LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch ((famR X I hX U Xg tr).A.leftGroupActionLift i t),
      ∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG (a.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP
  refine ⟨{ red := redQ X I U L eG i t
            red_surj := GlobalTheory.T.levelGroup_reduction_onto_finite_group_surjective X px I U L eG hI hV hL hG i t
            red_ker := fun q => redQ_eq_one_iff X I U L eG i t q
            act_eq := lemAct X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP }, fun q => ?_⟩
  exact eG_redQ X I U L eG i t q

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

theorem resChar_symm_conjPl (D : Formalism.BasicNotions.D7) (v : D.what₂.places.Pl) :
    D.what₂.places.resChar (D.plEq.symm (Formalism.DivisionValues.conjPl (D.plEq v))) = D.what₂.places.resChar v := by
  refine Formalism.MainNotions.Inhab.eq_resChar_of_mem D _ _ (D.what₂.places.resChar_prime v) ?_
  rw [Equiv.apply_symm_apply]
  show _ ∈ Ideal.map _ _
  have h := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.what₂.LL) (Formalism.MainNotions.Inhab.resChar_mem D v)
  rwa [map_natCast] at h

theorem resChar_mem_f0Primes : ∀ (K : Ctx) (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ v ∈ R3.placesWithNonzeroContentOrConj (w.D Z) (F0K K.s (w.D Z)), B.places.resChar v ∈ GlobalTheory.Mem.NonzeroPlacesOverPrimes.forcedContentSupportPrimes K B.toPre := by
  intro K B f T w Z v hv
  obtain ⟨j, y, hy, hne⟩ := hv
  have key : (w.D Z).what₂.places.resChar ((w.D Z).plEq.symm y) = B.places.resChar v := by
    rcases hy with h | h
    · rw [h]; exact congrArg (w.D Z).what₂.places.resChar ((w.D Z).plEq.symm_apply_apply v)
    · rw [h]; exact resChar_symm_conjPl (w.D Z) v
  unfold F0K FK at hne
  rw [key] at hne
  show B.places.resChar v ∈ ({(w.D Z).host.g 0, (w.D Z).host.g 1, (w.D Z).host.d} ∪
    Finset.range (⌊K.s.X'' (w.D Z).R.n⌋₊ + 1) : Finset ℕ)
  split_ifs at hne with h1 h2 h3
  · obtain ⟨i, hi⟩ := h1
    rw [hi]
    fin_cases i <;> simp
  · refine Finset.mem_union_left _ ?_
    unfold Host.cls primeClass at h2
    split_ifs at h2 with e1 e2 e3 <;> first | simp [e3] | exact absurd h2 (by decide)
  · exact Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h3.2)))
  · exact absurd rfl hne

end GlobalTheory.Mem.NonzeroPlacesOverPrimes
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LocSplice

theorem adAt_eq_of_prV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) {z z' : AfE F E}
    (h : Formalism.UG.prV (E := E) (P.under (𝓞 F)) z = Formalism.UG.prV (E := E) (P.under (𝓞 F)) z') :
    adAt F P z = adAt F P z' := by
  set v := P.under (𝓞 F)
  have h3 : adAt F P (Formalism.UG.P.afsplitEps E v) = 1 :=
    GlobalTheory.Mem.Col2.FullDt.adAt_eq_one_of_prV P (Formalism.UG.P.afsplit_prV_eps v)
  have e : ∀ w : AfE F E, adAt F P w =
      adAt F P (Formalism.UG.P.afsplitIE v (Formalism.UG.prV (E := E) v w)) := fun w => by
    rw [Formalism.UG.P.afsplit_decomp, map_mul, h3, one_mul]
  rw [e z, e z', h]

theorem map_conj_inv_mul {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (w w' A C : GL (Fin n) R)
    (h : ∀ r s, φ (w.1 r s) = φ (w'.1 r s)) (r s : Fin n) :
    φ ((((A⁻¹ * w * A)⁻¹ * C : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) r s) =
      φ ((((A⁻¹ * w' * A)⁻¹ * C : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) r s) := by
  have hΦ : Matrix.GeneralLinearGroup.map (n := Fin n) φ w = Matrix.GeneralLinearGroup.map φ w' := by
    apply Units.ext
    exact Matrix.ext h
  have h2 : Matrix.GeneralLinearGroup.map (n := Fin n) φ ((A⁻¹ * w * A)⁻¹ * C) =
      Matrix.GeneralLinearGroup.map φ ((A⁻¹ * w' * A)⁻¹ * C) := by
    simp only [map_mul, map_inv, hΦ]
  exact congrArg (fun z : GL (Fin n) S => (z : Matrix (Fin n) (Fin n) S) r s) h2

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ S.Uloc v → ∃ x ∈ S.U, ∀ (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep : SBof I a → ℕ) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P x g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g := by
  intro B X I hOk l Z a T i hi bad S P v hv κ hκ hloc
  refine ⟨Formalism.UG.P.afsplitU v (bc (prV (E := (I.rec7 l Z).host.E) v) κ) 1, ?_, ?_⟩
  · rw [S.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v _ _ _ _ (Formalism.UG.P.afsplit_bc_mem _ _ v κ hκ) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      rw [Formalism.UG.P.afsplit_right1]
      exact hloc
    · have h1 : bc (prV (E := (I.rec7 l Z).host.E) w) (Formalism.UG.P.afsplitU v (bc (prV (E := (I.rec7 l Z).host.E) v) κ) 1) = 1 := by
        apply Units.ext
        rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
        simp
      rw [h1]
      exact one_mem _
  · intro fb dep g hx
    have hseam := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a 0 0 P 1).1
    have hdict := fun z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) (dep P) P z).2.2
    have hvP : P.1.under (𝓞 B.host.F) = v := by
      apply HeightOneSpectrum.ext
      rw [hseam] at hv
      exact hv.symm
    unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hx ⊢
    have h1 := (hdict _).1 hx
    refine (hdict _).2 (fun r s => ?_)
    have h2 := h1 r s
    convert h2 using 3
    refine (map_conj_inv_mul _ _ _ _ _ (fun r s => ?_) r s).symm
    · apply adAt_eq_of_prV
      rw [hvP]
      exact congrFun (congrFun (Formalism.UG.P.afsplitC_prV (E := (I.rec7 l Z).host.E) v _ _) r) s

end GlobalTheory.Mem.Col2.AdT.LocSplice
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.level_coefficient_compatibility : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) := by
  first | exact @GlobalTheory.LevelActAnyField.actLev_of_levIs | exact GlobalTheory.LevelActAnyField.actLev_of_levIs | (intros; apply GlobalTheory.LevelActAnyField.actLev_of_levIs <;> assumption)
end
