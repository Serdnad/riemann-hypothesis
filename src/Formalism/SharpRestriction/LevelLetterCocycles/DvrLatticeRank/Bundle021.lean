module

public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle007
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfEqv
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfHyp
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

def WD : Prop :=
  ∀ τ ζ, Pt c ζ τ → ∀ {m m' : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T)
    (hy : ∀ j, y j ∈ NcS W T (c - 1)) (b : Fin m' → LetA O n) (z : Fin m' → W.DD T)
    (hz : ∀ k, z k ∈ NcS W T (c - 1)),
    ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ[O] mkL W T π' c (y j) (hy j) =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b k) ⊗ₜ[O] mkL W T π' c (z k) (hz k) →
    expS W T c ζ a y = expS W T c ζ b z

theorem expS_alg_mul (ζ : LL) (o : O) {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) :
    expS W T c ζ (fun j => algebraMap O (LetA O n) o * a j) y = algebraMap O LL o • expS W T c ζ a y := by
  funext i
  simp only [expS, serC, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [map_mul, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.coeff_C_mul, mul_smul]
  · rw [smul_zero]

theorem good_all (hwd : WD W T Pt π' c) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c)
    {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T} (hr : IsRepL W T π' Eπ h' c x a y) :
    ∀ τ ζ, Pt c ζ τ → ∀ i : ℤ, expS W T c ζ (fun j => (a j : LetA O n)) y i ∈
      Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - i) := by
  have hrep : x ∈ NLset W T Pt π' Eπ h' c := by
    clear hr
    induction hx using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      refine ⟨0, Fin.elim0, Fin.elim0, ⟨fun j => j.elim0, by simp⟩, fun τ ζ _ i => ?_⟩
      simp [expS]
    | add x₁ x₂ _ _ h₁ h₂ =>
      obtain ⟨m₁, a₁, y₁, ⟨hy₁, he₁⟩, hg₁⟩ := h₁
      obtain ⟨m₂, a₂, y₂, ⟨hy₂, he₂⟩, hg₂⟩ := h₂
      let z : Fin (m₁ + m₂) → ↥(NcS W T (c - 1)) :=
        Fin.append (fun j => ⟨y₁ j, hy₁ j⟩) (fun j => ⟨y₂ j, hy₂ j⟩)
      refine ⟨m₁ + m₂, Fin.append a₁ a₂, fun j => z j, ⟨fun j => (z j).2, ?_⟩, fun τ ζ hpt i => ?_⟩
      · rw [map_add (f := _), he₁, he₂, Fin.sum_univ_add]
        simp only [z, Fin.append_left, Fin.append_right]
      · simpa only [expS, Fin.sum_univ_add, z, Fin.append_left, Fin.append_right] using
          Submodule.add_mem _ (hg₁ τ ζ hpt i) (hg₂ τ ζ hpt i)
    | smul o x _ hx =>
      obtain ⟨m, a, y, ⟨hy, he⟩, hg⟩ := hx
      refine ⟨m, fun j => o • a j, y, ⟨hy, ?_⟩, fun τ ζ hpt i => ?_⟩
      · rw [map_smul, he, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [TensorProduct.smul_tmul', Subalgebra.coe_smul, mul_smul_comm]
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      · simp only [Subalgebra.coe_smul]
        simpa only [Algebra.smul_def, expS_alg_mul, Pi.smul_apply] using
          Submodule.smul_mem _ (algebraMap O LL o) (hg τ ζ hpt i)
  obtain ⟨m', a', y', ⟨hy', hx'⟩, hg⟩ := hrep
  obtain ⟨hy, hxr⟩ := hr
  intro τ ζ hpt i
  rw [hwd τ ζ hpt _ y hy _ y' hy' (hxr.symm.trans hx')]
  exact hg τ ζ hpt i

theorem nl_le : NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤ := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨m, a, y, ⟨hy, hx⟩, -⟩
  refine ⟨∑ j, a j ⊗ₜ ⟨mkL W T π' c (y j) (hy j), Submodule.mem_top⟩, ?_⟩

  rw [map_sum, hx]
  rfl

theorem nl_smulA {b : LetA O n} (hb : b ∈ W.AΔ) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c) :
    smulLA W T π' c b x ∈ NL W T Pt π' Eπ h' c := by
  have htmul (a : LetA O n) (e : W.EE) (z : LcQ W T π' c) :
      smulLA W T π' c a (e ⊗ₜ z) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ z := rfl
  have hcomm (x : LA W T π' c) :
      smulLA W T π' c (Eπ ^ h') (smulLA W T π' c b x) =
        smulLA W T π' c b (smulLA W T π' c (Eπ ^ h') x) := by
    induction x using TensorProduct.inductionOn with
    | tmul e z => simp only [htmul, mul_left_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, a, y, ⟨hy, he⟩, hg⟩ := hx
    refine Submodule.subset_span
      ⟨m, fun j => ⟨b * a j, W.AΔ.mul_mem hb (a j).2⟩, y, ⟨hy, ?_⟩, fun τ ζ hpt => ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hcomm, he, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htmul, ← map_mul]
      congr 2
      ring
    · exact MLB.goodF_mul W T c ζ τ h' b _ y (hg τ ζ hpt)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ _ hx

theorem nl_sat (hwd : WD W T Pt π' c) (hp : algebraMap O LL ((PD.p : ℕ) : O) ≠ 0)
    {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (k : ℕ)
    (hk : ((PD.p : ℕ) : O) ^ k • x ∈ NL W T Pt π' Eπ h' c) : x ∈ NL W T Pt π' Eπ h' c := by
  have hrep : ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y := by
    obtain ⟨t, ht⟩ := hx
    obtain ⟨m, a, s, rfl⟩ := MLE.exists_fin_sum t
    have hs : ∀ j, ∃ z : ↥(NcS W T (c - 1)), Submodule.Quotient.mk z =
        ((s j : ↥(⊤ : Submodule O _)) : LcQ W T π' c) := fun j => Submodule.Quotient.mk_surjective _ _
    choose z hz using hs
    refine ⟨m, a, fun j => z j, ⟨fun j => (z j).2, ?_⟩⟩

    rw [← ht, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ
      ((s j : ↥(⊤ : Submodule O _)) : LcQ W T π' c) = _
    rw [← hz j]
    rfl
  obtain ⟨m, a, y, hy, he⟩ := hrep
  let o : O := ((PD.p : ℕ) : O) ^ k
  have hr' : IsRepL W T π' Eπ h' c (o • x) (fun j => o • a j) y := by
    refine ⟨hy, ?_⟩
    rw [map_smul, he, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul', Subalgebra.coe_smul, mul_smul_comm]
    simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  have hg := good_all W T Pt π' Eπ h' c hwd hk hr'
  refine Submodule.subset_span ⟨m, a, y, ⟨hy, he⟩, fun τ ζ hpt i => ?_⟩
  have h1 := hg τ ζ hpt i
  simp only [Subalgebra.coe_smul] at h1
  simp only [Algebra.smul_def, expS_alg_mul, Pi.smul_apply] at h1
  have ho : algebraMap O LL o ≠ 0 := by simpa only [o, map_pow] using pow_ne_zero k hp
  exact (Submodule.smul_mem_iff _ ho).1 h1

end Generic

end Formalism.MainNotions.N.Ln34.MLF

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)


include Ct in
theorem framepf_data' [IsDomain O] (hι : Function.Injective (algebraMap O LL)) (hT : IsCrys PD T.ρ)
    (hs : W.s = 1) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (c : ZMod n)
    (hprim : ∀ τ ζ, Pt c ζ τ → IsPrimitiveRoot ζ PD.p) (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    {e s' : ℕ} {π' : LetA O n} {Ep : ZMod n → Polynomial O} (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' Ep)
    (hs' : 1 ≤ s') (h' M σ : ℕ) (hM1 : 1 ≤ M) (hM : 4 * h' ≤ s' * M) (l : ℕ) (hl : PD.p = l)
    (hyp : Nonempty (FramepfBas W T) ∧ (∀ j, PowerSeries.constantCoeff (π' j) = 0) ∧
      (∀ δ ∈ W.DelF, W.γA δ π' = π') ∧
      (∀ a ∈ W.AΔ, ∃! f : ZMod n → PowerSeries O, ∀ j, a j = PowerSeries.subst (π' j) (f j)) ∧
      (∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0) ∧
      IsUnit (algebraMap (LetA O n) W.EE π') ∧
      (∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) ∧ W.gamK = W.gam ∧
      ∃ Fs : PowerSeries O,
        W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs) ∧
        PowerSeries.constantCoeff Fs = ((W.χΓ W.gam : Oˣ) : O) ^ s' ∧
        (∀ y : ℕ, 1 ≤ y → (((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y ≠ 1) ∧
        ∃ aσ : O, (l : O) ^ σ = aσ * ∏ y ∈ Finset.Ico 1 M, ((((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y - 1))
    (hB : ∀ (Bs : FramepfBas W T) hπ0 hΔπ hR2 γ0 hu,
      FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M) :
    ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤, Ψ x ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c) ∧
      (∀ y ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c, Φ y ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤) ∧
      FramepfData W Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M σ c T hh Ψ Φ := by
  obtain ⟨⟨Bs⟩, hπ0, hΔπ, hR2, γ0, hu, hγN, hK, Fs, hFs, hF0, hne, aσ, haσ⟩ := hyp
  exact framepf_data Ct T hι hT hs Pt c hprim h4 hR hs' h' M σ hM1 hM hK
    Bs hπ0 hΔπ hR2 γ0 hu hγN Fs hFs hF0 hne aσ (by rw [hl]; exact haσ) (hB Bs hπ0 hΔπ hR2 γ0 hu)

end Local



theorem framepf_rec (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) (hh' : 1 ≤ h')
    (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (hB : ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
      ∀ (Bs : FramepfBas ((HW l).W K 1 LL hG) T) hπ0 hΔπ hR2 γ0 hu,
        IsUnit (algebraMap _ ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) →
        Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ → ∀ u ∈ ((HW l).W K 1 LL hG).AΔ,
        ((HW l).W K 1 LL hG).φA π' ^ MK l K h' = π' ^ MK l K h' * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ (4 * h') * u →
        FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h')) :
    FrameA ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h')
      (sigA l (sK l K) h') c := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hK : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam := ((HW l).W K 1 LL hG).gamK_eq_one hs hp2
  have hs' := ramification_quotient_pos l hl K LL hG
  have hM : 4 * h' ≤ sK l K * MK l K h' := by
    have hsR : (0 : ℝ) < (sK l K : ℝ) := by exact_mod_cast hs'
    have hc : (4 * h' : ℝ) / (sK l K : ℝ) ≤ (MK l K h' : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hsR] at hc
    have h4 : ((4 * h' : ℕ) : ℝ) ≤ ((sK l K * MK l K h' : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4
  have hM1 : 1 ≤ MK l K h' := by
    rcases Nat.eq_zero_or_pos (MK l K h') with h0 | h0
    · rw [h0, mul_zero] at hM
      omega
    · exact h0
  have hprim : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    intro τ ζ hpt
    rw [hpl]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  obtain ⟨u, huΔ, hφ⟩ := framepf_φπ hR hs h' _ hM
  obtain ⟨f, hfΔ, hf⟩ := framepf_γπ hR
  obtain ⟨t, htΔ, ht⟩ := framepf_γE hR hs ((HW l).W K 1 LL hG).gamK
  obtain ⟨t', ht'Δ, ht'⟩ := framepf_γE' hR hs ((HW l).W K 1 LL hG).gamK
  have huE := framepf_E_unit hR hs
  refine framepf_frameA _ _ π' _ h' _ _ c hK (framepf_π_unit hR) huE hR.1 u huΔ hφ hfΔ
    (by rw [hK]; exact hf) htΔ ht ht'Δ ht' fun T hT => ?_
  exact framepf_data' ((Cm l).C K 1 LL hG).tie T hι hT hs _ c hprim ((h1 l K 1 LL hG).2.2.2.1 T hT) hR
    hs' h' _ _ hM1 hM l hpl (framepf_hyps D HW F Cm h1 l hl K LL hG π' E hR T hT c h')
    fun Bs hπ0 hΔπ hR2 γ0 hu => hB T hT Bs hπ0 hΔπ hR2 γ0 hu huE (framepf_E_Δ hR) u huΔ hφ

end Formalism.MainNotions.N.Ln34

end
end
