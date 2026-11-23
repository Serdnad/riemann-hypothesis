module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle010
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module
open Formalism.MainNotions.N.FrobeniusPowerSeries (LiftsAt InFF InLpp)

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure CoresW [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) (CR : ℝ)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) : Prop where
  l5 : 5 ≤ PD.p
  hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)
  hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x
  inj : Function.Injective (algebraMap O LL)
  wr : Formalism.MainNotions.LiftingTheory.coreWR W CR
  H : Formalism.MainNotions.LiftingTheory.coreH W
  Tr : Formalism.MainNotions.LiftingTheory.coreTr W
  dc : Formalism.MainNotions.TruncatedSeriesCountingBounds.DcrisExactStrict PD LL
  relay : RelayCore W
  arc : ArcCore W
  arcL : ArcLCore W
  split : SplitCore W
  nn : UnivNNCore W
  univ : UnivCore PD W
  sat : SATcore W
  satP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W
  kLev : KillerLevCore W
  kMod : KillerModCore W
  r2 : R2
  P2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W
  P3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W
  P4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt
  ptEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
    ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ
  P5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W
  P9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W
  pi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u
  ext : ExtYCore PD W
  cj : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O
  c4 : Formalism.MainNotions.N.LetterConditionLocal W
  sec : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcSecMapCore W
  gl : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcGamLiftCore W
  hf : Formalism.MainNotions.N.FrobeniusPowerSeries.HorFrameCore W
  fl : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore W
  jq : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.LiftingTheory.Sur W F →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a
  jy : ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (cc : G → T₂.V),
    cc ∈ latticeCocycles T₂.L → IsCrys PD T₂.ρ → IsCrys PD Y.ρ → Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD Y.ρ τ a → a = 0 ∨ IsJumpV PD T₂.ρ τ a

end Core

section PPts

variable {l : ℕ} [Fact l.Prime]

theorem primitive_root_pow_l_eq_one (P : LocPrime l) : P.ζQ 1 ^ l = 1 := by
  have h := P.ζQ_succ 0
  simpa [P.ζQ_zero] using h

theorem primitive_root_mem_cyclotomic (P : LocPrime l) (K : FinExt l) : P.ζQ 1 ∈ Ks K 1 := by
  unfold Ks
  apply (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ K0 K ⊔ _)
  apply IntermediateField.subset_adjoin
  show P.ζQ 1 ^ (l ^ 1) = 1
  rw [pow_one]
  exact primitive_root_pow_l_eq_one P

def galoisEmbedding {K LL : FinExt l} (hG : Good K 1 LL) (g : GQ l) : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 where
  toFun y := ⟨g y, hG.2.2.2 (g.toAlgHom.comp (Ks K 1).val) y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by simp)

theorem galoisEmbedding_coe {K LL : FinExt l} (hG : Good K 1 LL) (g : GQ l) (y : ↥(Ks K 1)) :
    ((galoisEmbedding hG g y : ↥LL.1) : Om l) = g y := rfl

theorem exists_galois_extending_algHom {F : IntermediateField ℚ_[l] (Om l)} (τ : F →ₐ[ℚ_[l]] Om l) :
    ∃ g : GQ l, ∀ x : F, g x = τ x := by
  classical
  let φ : Om l →ₐ[ℚ_[l]] Om l := τ.liftNormal (Om l)
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun x => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  have h := τ.liftNormal_commutes (Om l) x
  simpa using h

end PPts

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

structure UsedJ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop where
  a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F
  a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F
  c4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F

theorem ptEx_at (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] :
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
      Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hG) τ i →
      ∃ ζ : ↥LL.1, ζ ^ ((D.loc l).PD K).p = 1 ∧ ζ ≠ 1 ∧ Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG i ζ τ := by
  intro i τ hτ
  classical
  have hτ' := hτ
  unfold Formalism.MainNotions.LiftingTheory.Over at hτ'
  obtain ⟨g, hg⟩ := exists_galois_extending_algHom ((LL.1).val.comp τ)
  have hz := primitive_root_mem_cyclotomic (D.loc l) K
  have h1 : ((galoisEmbedding hG g ⟨(D.loc l).ζQ 1, hz⟩ : ↥LL.1) : Om l) = g ((D.loc l).ζQ 1) :=
    galoisEmbedding_coe hG g _
  refine ⟨galoisEmbedding hG g ⟨(D.loc l).ζQ 1, hz⟩, ?_, ?_, ?_⟩
  · rw [(D.loc l).PD_p K]
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, h1, OneMemClass.coe_one]
    rw [← map_pow, primitive_root_pow_l_eq_one, map_one]
  · intro h
    apply (D.loc l).ζQ_one
    have h2 := congrArg (fun z : ↥LL.1 => (z : Om l)) h
    simp only [h1, OneMemClass.coe_one] at h2
    exact g.injective (h2.trans (map_one g).symm)
  · unfold Formalism.MainNotions.DeltaInvariantLattices.ptK Formalism.BasicNotions.LocHW.IsPt
    refine ⟨galoisEmbedding hG g, ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
    · rw [← hτ']
      apply Subtype.ext
      rw [galoisEmbedding_coe, hxy]
      exact hg (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x)
    · exact congrArg (galoisEmbedding hG g) (Subtype.ext hy)
    · apply Subtype.ext
      rw [galoisEmbedding_coe, hxy]
      exact (hg x).symm

end Record

end Formalism.MainNotions.N.Ln17
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.AKill

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem hmax_le [NeZero n] (Mi hi : ZMod n → ℕ) (j : ZMod n) :
    Mi j + hi j ≤ Formalism.MainNotions.LiftingTheory.Hmax n Mi hi := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax
  have h := Finset.le_sup (f := fun k : ℕ => Mi k + hi k) (Finset.mem_range.2 (ZMod.val_lt j))
  simp only [ZMod.natCast_zmod_val] at h
  exact h

theorem ai_le [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR) (a : ZMod n) :
    (Formalism.MainNotions.LiftingTheory.AI W F a : ℝ) ≤ ((size (a + 1) : ℝ) + S + η) / PD.p + 5 / 2 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
      (¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (a + 2) →
        (Formalism.MainNotions.LiftingTheory.AI W F a : ℝ) ≤ ((size (a + 1) : ℝ) + S + η) / PD.p + 2 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size) := by
  obtain ⟨hp11, hSet, hwb, hηb, hSb, ⟨j, hj⟩⟩ := hB
  obtain ⟨hcase, hSur, hηs, hJA, _hlow, hnt, _hJL⟩ := hSet
  set h := Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size with hhdef
  have hF : (∀ i, size i + S ≤ h) ∧ w + S ≤ h := by
    rw [hhdef]
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
    split_ifs with hex
    · refine ⟨fun i => ?_, by omega⟩
      by_cases ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i
      · have := ht.2; omega
      · have := hnt i ht; omega
    · push Not at hex
      exact ⟨fun i => by have := hnt i (hex i); omega, le_rfl⟩
  have hη1 : η + 1 ≤ h := by
    have := hnt j hj
    have := hηs j
    have := hF.2
    omega
  let Mi' : ZMod n → ℕ := fun i => if up i then η else size i + S
  let hi' : ZMod n → ℕ := fun i => if up i then size i + S else η
  have hbox : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi' hi' := by
    intro i τ hτ x hx
    have h1 := hJA i τ hτ x hx
    have h2 := hηs i
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hHbox : ∀ i, Mi' i + hi' i ≤ h + η := by
    intro i
    have := hF.1 i
    cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hbx : ∀ i, Mi' i + hi' i = size i + S + η := by
    intro i
    cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  obtain ⟨hs, -⟩ := hWR hcase T₁ T₂ F Mi' hi' hSur hbox a
  set H := Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' with hHdef
  have hHle : H ≤ h + η := Finset.sup_le fun k _ => hHbox _
  have hcW : (Formalism.MainNotions.LiftingTheory.cH PD.p H : ℝ) = (cW PD.p H : ℝ) := rfl
  have hx : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hA : (Formalism.MainNotions.LiftingTheory.AI W F a : ℝ) ≤ (Formalism.MainNotions.LiftingTheory.sI W F a : ℝ) / ((PD.p : ℝ) - 1) + 1 := by
    unfold Formalism.MainNotions.LiftingTheory.AI
    have h0 : 0 ≤ (Formalism.MainNotions.LiftingTheory.sI W F a : ℝ) / ((PD.p : ℝ) - 1) :=
      div_nonneg (Nat.cast_nonneg _) (by linarith)
    exact (Nat.ceil_lt_add_one h0).le
  have hH₁ : Mi' (a + 1) + hi' (a + 1) ≤ h + η := hHbox _
  have hH₁r : ((Mi' (a + 1) + hi' (a + 1) : ℕ) : ℝ) = (size (a + 1) : ℝ) + S + η := by
    rw [hbx]; push_cast; ring
  have eSg : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p h w S η := rfl
  let fx : ℕ → ℝ := fun x => ((Mi' (a + ((x + 1 : ℕ) : ZMod n)) + hi' (a + ((x + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) +
      Formalism.MainNotions.LiftingTheory.cH PD.p H + 3
  have hf0 : ∀ x, 0 ≤ fx x := fun x => by positivity
  have hfH : ∀ x, fx x ≤ (H : ℝ) + cW PD.p H + 3 := by
    intro x
    have := hmax_le Mi' hi' (a + ((x + 1 : ℕ) : ZMod n))
    have h' : (((Mi' (a + ((x + 1 : ℕ) : ZMod n)) + hi' (a + ((x + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)) ≤ H := by
      exact_mod_cast this
    show _ + _ + _ ≤ _
    rw [hcW]; linarith
  have hf0' : fx 0 ≤ ((Mi' (a + 1) + hi' (a + 1) : ℕ) : ℝ) + cW PD.p H + 3 := by
    simp [fx, hcW]
  refine ⟨?_, fun hnt2 => ?_⟩
  · have ht := tsum_three PD.p hp11 fx _ ((H : ℝ) + cW PD.p H + 3) ((H : ℝ) + cW PD.p H + 3) hf0 hf0'
      (hfH 1) (fun x _ => hfH x)
    have hst := hs.trans ht
    have hs' : (Formalism.MainNotions.LiftingTheory.sI W F a : ℝ) ≤ (((Mi' (a + 1) + hi' (a + 1) : ℕ) : ℝ) + cW PD.p H + 3) +
        ((H : ℝ) + cW PD.p H + 3) / ((PD.p : ℝ) - 2) := by
      have h1 : (PD.p : ℝ) - 1 ≠ 0 := by intro h; linarith
      have h2 : (PD.p : ℝ) - 2 ≠ 0 := by intro h; linarith
      have e : ∀ X : ℝ, X / ((PD.p : ℝ) - 1) + X / (((PD.p : ℝ) - 1) * ((PD.p : ℝ) - 2)) =
          X / ((PD.p : ℝ) - 2) := by
        intro X; field_simp; ring
      linarith [e ((H : ℝ) + cW PD.p H + 3)]
    have := Aa_le PD.p hp11 h w S η H (Mi' (a + 1) + hi' (a + 1)) hη1 hHle hH₁ _ _ hs' hA
    rw [hH₁r] at this
    rw [eSg]; exact this
  · have hH₂ : Mi' (a + 2) + hi' (a + 2) ≤ w + S + η := by
      have := hnt (a + 2) hnt2
      rw [hbx]; omega
    have hf1 : fx 1 ≤ ((Mi' (a + 2) + hi' (a + 2) : ℕ) : ℝ) + cW PD.p H + 3 := by
      have e2 : a + ((1 + 1 : ℕ) : ZMod n) = a + 2 := by push_cast; ring
      simp only [fx, e2, hcW]; exact le_rfl
    have ht := tsum_three PD.p hp11 fx _ _ ((H : ℝ) + cW PD.p H + 3) hf0 hf0' hf1 (fun x _ => hfH x)
    have hst := hs.trans ht
    have := Aa_cut_le PD.p hp11 h w S η H (Mi' (a + 1) + hi' (a + 1)) (Mi' (a + 2) + hi' (a + 2)) hη1 hHle
      hH₁ hH₂ _ _ hst hA
    rw [hH₁r] at this
    rw [eSg]; exact this

end Formalism.MainNotions.N.FrobeniusPowerSeries.AKill
end
end
