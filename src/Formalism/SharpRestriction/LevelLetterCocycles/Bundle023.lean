module

public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle020
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
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
import Formalism.DistinguishedUnitIdeals.ExistsConstOfInvariantMod

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

section LemGA0

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lemGA0_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (R := Qp) (M := T.V)
    (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem lemGA0_one_root (l : ℕ) : ∃ j : ℕ, IsPrimitiveRoot (1 : LL) (l ^ j) := ⟨0, by simpa using IsPrimitiveRoot.one⟩

theorem lemGA0_cc_letπ (W : LocWach PD LL O v n) (i : ZMod n) :
    PowerSeries.constantCoeff (W.lev i 1 (letπ : LetA O n)) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 (lemGA0_one_root PD.p)
  have h := congrArg PowerSeries.constantCoeff hE
  simp only [map_add (f := _), map_one, hE0, one_mul] at h
  linear_combination h

theorem lemGA0_cc_π₀₁ (W : LocWach PD LL O v n) (hcard : W.DelF.card = PD.p - 1) (hp : 1 ≤ PD.p) :
    PowerSeries.constantCoeff W.π₀₁ = 0 := by
  unfold LocWach.π₀₁
  have h2 : ∀ δ, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = (0 : O) := fun δ => (W.γ₀_X δ).1

  simp only [map_add (f := _), map_sub, map_one, map_natCast, map_sum, h2, add_zero, Finset.sum_const,
  nsmul_eq_mul, mul_one, hcard]
  push_cast [Nat.cast_sub hp]
  ring

theorem lemGA0_cc_π₀ (W : LocWach PD LL O v n) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 W.π₀) = 0 := by
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr h0
  have e : W.π₀ = (letπ : LetA O n) * (fun _ => g) := by
    funext j
    show W.π₀₁ = PowerSeries.X * g
    exact hg
  rw [e, map_mul, map_mul, lemGA0_cc_letπ, zero_mul]

theorem lemGA0_cc_qp (W : LocWach PD LL O v n) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W)) = (PD.p : LL) := by
  unfold Formalism.MainNotions.LiftingTheory.qp
  rw [map_add (f := _), map_natCast, map_add (f := _), lemGA0_cc_π₀ W i h0, map_natCast, zero_add]

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]

theorem lemGA0_cc_pk (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.pk W 1)) = (PD.p : LL) := by
  have e : Formalism.MainNotions.LiftingTheory.pk W 1 = W.φA (Formalism.MainNotions.LiftingTheory.qp W) := by
    unfold Formalism.MainNotions.LiftingTheory.pk; rw [pow_one]
  rw [e, C.lev_φ i 1 (lemGA0_one_root PD.p) (Formalism.MainNotions.LiftingTheory.qp W), one_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, lemGA0_cc_qp W (i - 1) h0]

theorem lemGA0_conv_vanish {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M)
    (hf : PowerSeries.constantCoeff f ≠ 0) (hsupp : ∃ m : ℤ, ∀ k < m, d k = 0)
    (hneg : ∀ r : ℤ, r < 0 → ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (r - j) = 0) :
    ∀ r : ℤ, r < 0 → d r = 0 := by
  obtain ⟨m, hm⟩ := hsupp
  have key : ∀ t : ℕ, ∀ r : ℤ, r < m + t → r < 0 → d r = 0 := by
    intro t
    induction t with
    | zero => intro r hr _; exact hm r (by simpa using hr)
    | succ t ih =>
      intro r hr hr0
      by_cases hlt : r < m + t
      · exact ih r hlt hr0
      · have hs : ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (r - j) =
            PowerSeries.coeff 0 f • d (r - ((0 : ℕ) : ℤ)) := by
          apply finsum_eq_single _ 0
          intro j hj
          rw [ih (r - j) (by push_cast at hr; omega) (by omega), smul_zero]
        have h := hneg r hr0
        rw [hs, Nat.cast_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
        have h' := congrArg (fun z => (PowerSeries.constantCoeff f)⁻¹ • z) h
        simpa [inv_smul_smul₀ hf] using h'
  intro r hr
  by_cases h : r < m
  · exact hm r h
  · apply key (r - m + 1).toNat r _ hr
    rw [Int.toNat_of_nonneg (by omega)]
    omega

theorem lemGA0_conv_zero {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M)
    (hd : ∀ r : ℤ, r < 0 → d r = 0) :
    ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (0 - j) = PowerSeries.constantCoeff f • d 0 := by
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [hd _ (by have : (0 : ℕ) < j := Nat.pos_of_ne_zero hj; omega), smul_zero]

theorem lemGA0_of_tools [NeZero n] (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) (hT : Formalism.MainNotions.CrystallineLiftingInputs.THor W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    LemGA_0 W := by
  intro d T₁ T₂ F b S η m hS i hi y hy hyD la hla x hx hxD hxe
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hS.2.2.2.2.2.1
  have hcr : IsCrys PD T₂.ρ := by unfold Formalism.MainNotions.LiftingTheory.Sur at hsur; exact hsur.2.1
  have hp0 : (PD.p : LL) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
    have hpos : 0 < PD.p := by omega
    have : NeZero PD.p := ⟨hpos.ne'⟩
    exact (hζ.neZero').out

  have hfr : finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq, Module.finrank_self]
  obtain ⟨hcard, -, h9K⟩ := h9 T₂ hcr hA.2.1 hA.2.2
  rw [hfr, Nat.div_one] at hcard
  have h0 : PowerSeries.constantCoeff W.π₀₁ = 0 := lemGA0_cc_π₀₁ W hcard (by omega)
  obtain ⟨-, hmod⟩ := h9K hfr
  have hyI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ (i - 2) y := by
    refine ⟨hyD, ⟨0, 0, by simpa using hy⟩, ?_⟩
    obtain ⟨x', hx', he⟩ := hmod.2 y ⟨hy, hyD.2⟩
    exact ⟨x', hx'.1, hx'.2, by rw [pow_one]; exact he⟩

  have hk : (Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) • la ∈ W.N T₂ := by
    rw [pow_zero, one_mul, ← hxe]
    exact Submodule.smul_mem _ _ hx
  have hTH := hT hA hp11 2 1 (2 * (hpar n b S + η)) (lemG_sig PD.p (hpar n b S + η))
    (Or.inr ⟨rfl, rfl, rfl⟩) T₂ hcr (i - 2) y la hy hyI hla.1 1 ((PD.p - 1) * 1) 0
    (Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) hk (Or.inr ⟨rfl, rfl⟩)
  have hneg := hTH.1
  have h0v := hTH.2 0 (by omega)
  have hi2 : i - 2 + ((2 : ℕ) : ZMod n) = i := by rw [Nat.cast_ofNat, sub_add_cancel]
  have hsub : (⟨(Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) • la, hk⟩ : ↥(W.N T₂)) =
      (Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂)) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, pow_zero, one_mul]
    exact hxe.symm
  rw [hi2, hsub] at hneg h0v
  rw [Nat.cast_zero] at h0v

  have hsm : ∀ r : ℤ, W.levN T₂ i 1 ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂))) r =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) •
        W.levN T₂ i 1 ⟨x, hx⟩ (r - j) :=
    fun r => W.levN_smul T₂ i 1 _ _ r
  have hccb : PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) = (PD.p : LL) ^ b i := by
    rw [map_pow, map_pow, lemGA0_cc_qp W i h0]
  have hxneg : ∀ r : ℤ, r < 0 → W.levN T₂ i 1 ⟨x, hx⟩ r = 0 :=
    lemGA0_conv_vanish (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) (W.levN T₂ i 1 ⟨x, hx⟩)
      (by rw [hccb]; exact pow_ne_zero _ hp0) (W.levN_supp T₂ i 1 _)
      (fun r hr => by rw [← hsm r]; exact hneg r hr)
  have he : ((letE i : LetA O n) • (⟨x, hx⟩ : ↥(W.N T₂))) = ⟨x, hx⟩ := Subtype.ext hxD.1
  have hL : W.levN T₂ i 1 ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂))) 0 =
      (PD.p : LL) ^ b i • ιV PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨x, hx⟩) := by
    rw [hsm, lemGA0_conv_zero _ _ hxneg, hccb, C.levN_eq, ← C.cmp_eq T₂ hcr i, he]
  have hcch : PowerSeries.coeff 0 (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S))) =
      (PD.p : LL) ^ (b (i - 1) + S) := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, pow_zero, one_mul, map_pow, map_pow,
      lemGA0_cc_pk W C i h0]
  have hmain : (PD.p : LL) ^ b i • W.cmp T₂ ⟨x, hx⟩ =
      (PD.p : LL) ^ (b (i - 1) + S) • ((PD.p : LL) ^ lemG_sig PD.p (hpar n b S + η) •
        (φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩)) := by
    apply lemGA0_ιV_inj (PD := PD) T₂
    rw [map_smul, map_smul, map_smul, ← hL, h0v, hcch]
  rw [← inv_smul_smul₀ (pow_ne_zero (b i) hp0) (W.cmp T₂ ⟨x, hx⟩), hmain, smul_smul, smul_smul,
    zpow_sub₀ hp0, zpow_add₀ hp0, zpow_natCast, zpow_natCast, zpow_natCast]
  congr 1
  ring

end LemGA0

end Formalism.MainNotions.RamifiedCoefficientChains.S9
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
    (W : LocWach PD LL O v n)

def LemC (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n) : Prop :=
  ∀ x (hx : x ∈ NcS W T (c - 1)), (∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true →
    x ∈ FilL W T Pt c τ (b τ)) → ∀ f, IsCoord W Pt π' Eπ h' S up b c f →
    f ⊗ₜ mkL W T π' c x hx ∈ InvL W T Pt π' Eπ h' c ⊤

end Local

section Record

end Record

end Formalism.MainNotions.N.Ln34

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
    (W : LocWach PD LL O v n)

def ExpL (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (ζ : LL) (x : LA W T π' c)
    (f : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  (∃ m₀ : ℤ, ∀ i < m₀, f i = 0) ∧ ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y ∧
    ∀ i, serMul (W.lev c ζ (Eπ ^ h')) f i = expS W T c ζ (fun j => (a j : LetA O n)) y i

abbrev QL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Type :=
  ↥(LamLA W T π' Eπ h' c ⊤) ⧸ (piNL W T Pt π' Eπ h' c 1).comap (LamLA W T π' Eπ h' c ⊤).subtype

def ModelL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M : ℕ) (c : ZMod n) : Prop :=
  NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤ ∧
  (∀ x ∈ NL W T Pt π' Eπ h' c, γLA W T π' c x ∈ NL W T Pt π' Eπ h' c) ∧
  (∀ a ∈ W.AΔ, ∀ x ∈ NL W T Pt π' Eπ h' c, smulLA W T π' c a x ∈ NL W T Pt π' Eπ h' c) ∧
  (LinearMap.range (toLA W T π' c ⊤)).map (smulLA W T π' c (Eπ ^ h')) ≤ NL W T Pt π' Eπ h' c ∧
  (∀ x ∈ LamLA W T π' Eπ h' c ⊤, ∀ k : ℕ, ((PD.p : ℕ) : O) ^ k • x ∈ NL W T Pt π' Eπ h' c →
    x ∈ NL W T Pt π' Eπ h' c) ∧
  JLA W T π' Eπ h' M c ≤ piNL W T Pt π' Eπ h' c M ∧
  ∀ x ∈ LamLA W T π' Eπ h' c ⊤, γLA W T π' c x - x ∈ NL W T Pt π' Eπ h' c →
    ∀ τ ζ, Pt c ζ τ → ∀ f, ExpL W T π' Eπ h' c ζ x f → ∀ i : ℤ, i ≠ 0 →
      f i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-i)

def ModelQ (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Prop :=
  Module.Finite O (QL W T Pt π' Eπ h' c) ∧
    ∀ (a : O) (q : QL W T Pt π' Eπ h' c), a ≠ 0 → a • q = 0 → q = 0

def ModelK {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (π' : LetA O n) (ρ : ℕ) (c : ZMod n) : Prop :=
  ∀ y ∈ NcS W T₂ (c - 1), ∃ x ∈ NcS W T₁ (c - 1), W.map F x - ((PD.p : ℕ) : O) ^ ρ • y ∈ PiNS W T₂ π' 1

end Local

section Record

def modelLR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, ModelL ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c

def modelQR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, ModelQ ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def modelKR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T₁.ρ →
      IsCrys ((D.loc l).PD K) T₂.ρ → F.Onto → (∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h')) → ∀ c, ModelK ((HW l).W K 1 LL hG) F π' (rhoA l (eK K) h') c

end Record

def ModelLStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelLR D HW

def ModelQStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelQR D HW

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)


open Classical in
def SecondPropositionRingInput (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) : Prop :=
  IsUnit (algebraMap (LetA O n) W.EE π') ∧ IsUnit (algebraMap (LetA O n) W.EE Eπ) ∧
  (∃ g ∈ W.AΔ, W.γA W.gamK π' = π' * g) ∧
  ∃ ν ∈ W.AΔ, ν * W.γA W.gamK (Eπ ^ h') = Eπ ^ h' ∧
  ∃ (N : ℕ) (f : ℕ → LetA O n) (cc : ℕ → O),
    (∀ k, f k ∈ W.AΔ) ∧
    (letE c : LetA O n) * ∏ k ∈ Finset.range N, f k = (letE c : LetA O n) * (π' * Eπ ^ (2 * h')) ∧
    (∀ k < N, ∀ a ∈ W.AΔ, ∃ (a₀ : O) (b : LetA O n), b ∈ W.AΔ ∧
      (letE c : LetA O n) * a = (letE c : LetA O n) * (algebraMap O (LetA O n) a₀ + f k * b)) ∧
    (∀ k < N, ∀ a ∈ W.AΔ, ∃ b ∈ W.AΔ,
      (letE c : LetA O n) * (ν * W.γA W.gamK ((∏ j ∈ Finset.range k, f j) * a) -
          algebraMap O (LetA O n) (cc k) * ((∏ j ∈ Finset.range k, f j) * a)) =
        (letE c : LetA O n) * ((∏ j ∈ Finset.range (k + 1), f j) * b)) ∧
    ((Finset.range N).filter fun k => cc k = 1).card ≤ finrank K₀ K + 1

end Local

def secondPropositionRingAll (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ c, SecondPropositionRingInput ((HW l).W K 1 LL hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def SecondRingHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → secondPropositionRingAll D HW

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def SecondPropositionHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → u2R D HW

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def UnivLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (Fo : FonOf D.loc D.locA HW), HerrClassMapsLocal D HW Fo → dvdR →
    invLiftR D HW → classMapR D HW → frameR D HW → modelFR D HW → u1R D HW → kapPiR D HW →
    u2R D HW → DownSlotProposition D HW → UpSlotProposition D HW → MixedSlotProposition D HW → univR D HW

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

def CoordSteps (hR : Ring9 W) (e : W.DD W.one) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∃ (C₁ : Coord W (baseIdOf hR) T₁) (C₂ : Coord W (baseIdOf hR) T₂) (C₀ : Coord W (baseIdOf hR) W.one)
      (_h : CoordHom C₁ C₂ F) (e₀ : C₀.V), ∀ i, C₀.t i e₀ = (letE i : LetA O n) • e

end Formalism.MainNotions.N.Ln03
end
end
