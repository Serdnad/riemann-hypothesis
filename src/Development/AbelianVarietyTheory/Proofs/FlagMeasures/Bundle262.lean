module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle038
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle206
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle106
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSquareIdxNOfCovBy
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle249
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle231
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle036
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIndependentOfQuotientMeasure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle223
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle252
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsFolnerSequenceBessel
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle076
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle047
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle082
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle251
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021

@[expose] public section

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.SubCount

theorem encard_biUnion_le_sum {ι β : Type} (s : Finset ι) (Y : ι → Set β) :
    ((⋃ i ∈ s, Y i).encard : ℝ≥0∞) ≤ ∑ i ∈ s, ((Y i).encard : ℝ≥0∞) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.set_biUnion_insert]
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_union_le _ _)) ?_
    rw [ENat.toENNReal_add]
    gcongr

theorem encard_biUnion_le_mul {ι β : Type} (S : Set ι) (Y : ι → Set β) (c : ℝ≥0∞) (hc : c ≠ 0)
    (h : ∀ i ∈ S, ((Y i).encard : ℝ≥0∞) ≤ c) :
    ((⋃ i ∈ S, Y i).encard : ℝ≥0∞) ≤ (S.encard : ℝ≥0∞) * c := by
  rcases S.finite_or_infinite with hS | hS
  · lift S to Finset ι using hS
    refine (encard_biUnion_le_sum S Y).trans ((Finset.sum_le_card_nsmul S _ c h).trans (le_of_eq ?_))
    rw [Set.encard_coe_eq_coe_finsetCard, nsmul_eq_mul]
    simp
  · rw [hS.encard_eq, ENat.toENNReal_top, ENNReal.top_mul hc]
    exact le_top

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]
  [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]

theorem index_eq (M : Submodule (𝓞 K) V) (hM : M.FG) (j : ℕ) (hj : 1 ≤ j) :
    (({P : Submodule (𝓞 K) V | P ≤ M ∧ Nat.card (M ⧸ P.comap M.subtype) = j}).encard : ℝ≥0∞) ≤
      ENNReal.ofReal ((j : ℝ) ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K))) := by
  haveI : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  haveI : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  haveI : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have hr : finrank (𝓞 K) M ≤ finrank K V := by
    refine Module.finrank_le_of_rank_le ((Submodule.rank_le M).trans (le_of_eq ?_))
    rw [Module.finrank_eq_rank, IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl]
  obtain ⟨h1, h2⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2a K M (finrank K V) j hj hr
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal h2)
  rw [ENNReal.ofReal_natCast, ← ENat.toENNReal_coe, h1.cast_ncard_eq, ENat.toENNReal_le]
  refine Set.encard_le_encard_of_injOn (f := fun P => P.comap M.subtype) (fun P hP => hP.2) ?_
  intro P hP Q hQ e
  have := congrArg (Submodule.map M.subtype) e
  simpa only [Submodule.map_comap_subtype, inf_eq_right.2 hP.1, inf_eq_right.2 hQ.1] using this

theorem index_le (M : Submodule (𝓞 K) V) (hM : M.FG) (x : ℝ) (hx : 0 < x) :
    (({P : Submodule (𝓞 K) V | P ≤ M ∧ 1 ≤ Nat.card (M ⧸ P.comap M.subtype) ∧
      (Nat.card (M ⧸ P.comap M.subtype) : ℝ) ≤ x}).encard : ℝ≥0∞) ≤
      ENNReal.ofReal (x ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K) + 1)) := by
  have he : 0 ≤ (finrank K V : ℝ) + Real.logb 2 (finrank ℚ K) :=
    add_nonneg (Nat.cast_nonneg _) (Real.logb_nonneg one_lt_two (by exact_mod_cast Module.finrank_pos))
  calc _ ≤ ((⋃ j ∈ Finset.Icc 1 ⌊x⌋₊,
        {P : Submodule (𝓞 K) V | P ≤ M ∧ Nat.card (M ⧸ P.comap M.subtype) = j}).encard : ℝ≥0∞) := by
        refine ENat.toENNReal_le.2 (Set.encard_le_encard fun P hP => ?_)
        simp only [Set.mem_iUnion]
        exact ⟨_, Finset.mem_Icc.2 ⟨hP.2.1, Nat.le_floor hP.2.2⟩, hP.1, rfl⟩
    _ ≤ _ := encard_biUnion_le_sum _ _
    _ ≤ (Finset.Icc 1 ⌊x⌋₊).card • ENNReal.ofReal (x ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K))) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
        refine (index_eq M hM j h1).trans (ENNReal.ofReal_le_ofReal ?_)
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) ((Nat.le_floor_iff hx.le).1 h2) he
    _ ≤ _ := by
        rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Real.rpow_add_one hx.ne',
          ENNReal.ofReal_mul' hx.le, mul_comm, ← ENNReal.ofReal_natCast]
        gcongr
        exact Nat.floor_le hx.le

end Index

theorem main : ∀ (D : D7) (L : LatW D), IsPosDef (D.sp.X 0).hT → finrank D.host.E (D.sp.X 0).V = D.R.k → L.FG → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT L → ∀ (n : ℕ) (De : ℝ), 1 ≤ De → (Set.encard {P : LatW D | P ≤ L ∧ rkW D P = n ∧ detW D P ≤ De} : ℝ≥0∞) ≤ ∑ de ∈ Finset.Icc 1 ⌊De⌋₊, (cntPrim (D.sp.X 0).hT L n de : ℝ≥0∞) * ENNReal.ofReal ((De / (de : ℝ)) ^ ((D.R.k : ℝ) + lg2f D.R.f + 1)) := by
  intro D L hpos hk hL hint n De hDe
  have hf : ((finrank ℚ D.host.E : ℕ) : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [(GlobalTheory.real_places_facts D).2.1]; push_cast; rfl
  calc _ ≤ ((⋃ de ∈ Finset.Icc 1 ⌊De⌋₊, ⋃ M ∈ PrimSubs (D.sp.X 0).hT L n de,
        {P : LatW D | P ≤ M ∧ 1 ≤ Nat.card (M ⧸ P.comap M.subtype) ∧
          (Nat.card (M ⧸ P.comap M.subtype) : ℝ) ≤ De / (de : ℝ)}).encard : ℝ≥0∞) := by
        refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
        rintro P ⟨hP, hr, hd⟩
        have hS : sat D L P ≤ L := inf_le_left
        have hPS : P ≤ sat D L P := fun x hx => ⟨hP hx, Submodule.subset_span hx⟩
        have hfg : (sat D L P).FG := hL.of_le hS
        have hi : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (sat D L P) :=
          fun x hx y hy => hint x (hS hx) y (hS hy)
        have hsp : Submodule.span D.host.E (sat D L P : Set (D.sp.X 0).V) =
            Submodule.span D.host.E (P : Set (D.sp.X 0).V) :=
          le_antisymm (Submodule.span_le.2 fun x hx => hx.2) (Submodule.span_mono hPS)
        have hrk : rkW D P = rkW D (sat D L P) := by unfold rkW; rw [hsp]
        obtain ⟨h4, h5⟩ := (GlobalTheory.LoopC.DetCard.main D _ hfg hpos hi).2.2 P hPS hrk
        have ha : ∀ x : (D.sp.X 0).V, (D.sp.X 0).hT x x = 0 → x = 0 := by
          intro x hx
          by_contra h0
          obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
          have := hpos τ x h0
          rw [hx] at this
          simp at this
        obtain ⟨de, h1, h2⟩ := GlobalTheory.Mass.DetNat.main D.host.E (D.sp.X 0) D.sp.cm.cmUnram.2.1
          (GlobalTheory.InertSquareNorm.isSquare_absNorm _ D.sp.cm.cmUnram) ha _ hfg fun x hx =>
            ⟨(Formalism.HermitianLatticesTheory.dualBasic_mem_dual _ _ _).2 fun y hy => hi y hy x hx, Submodule.subset_span hx⟩
        have h3 : detW D (sat D L P) = de := h2
        have hde : (1 : ℝ) ≤ de := by exact_mod_cast h1
        have hj : (1 : ℝ) ≤ idxW D (sat D L P) P := by exact_mod_cast h4
        rw [h5, h3] at hd
        simp only [Set.mem_iUnion]
        refine ⟨de, Finset.mem_Icc.2 ⟨h1, Nat.le_floor (by nlinarith)⟩, sat D L P,
          ⟨⟨hS, by rw [hsp]; rfl⟩, hrk.symm.trans hr, h2⟩, hPS, h4, ?_⟩
        rw [le_div_iff₀' (by linarith)]
        exact hd
    _ ≤ _ := encard_biUnion_le_sum _ _
    _ ≤ _ := by
        refine Finset.sum_le_sum fun de hde => ?_
        have h1 : (0 : ℝ) < de := by exact_mod_cast (Finset.mem_Icc.1 hde).1
        have hx : 0 < De / (de : ℝ) := div_pos (by linarith) h1
        refine encard_biUnion_le_mul _ _ _ (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hx _)).ne' fun M hM => ?_
        have := index_le (K := D.host.E) M (hL.of_le hM.1.1) _ hx
        rwa [hk, hf] at this

end GlobalTheory.LoopC.SubCount
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveTerm
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem cj_mem_O {c : E} (hc : c ∈ L.O) : L.cj c ∈ L.O := by
  rw [L.O_def] at hc ⊢
  exact hc.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem top_coord (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (w : S.GLV) (hw : w ∈ S.Nof g) (j : Fin r) (x : S.V) (hx : x ∈ S.spanTo g (j + 1))
    (al : Fin (r + 1) → E) (e : x = ∑ i, al i • w (g i)) :
    S.h x (gs j) = al j.castSucc := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at hw
  obtain ⟨⟨-, h1⟩, -⟩ := hw
  have e' : x = w (∑ i, al i • g i) := by simp [e]
  have hz : ∑ i, al i • g i ∈ S.spanTo g (j + 1) := ((h1 j).1 _).1 (e' ▸ hx)
  have hB := (h1 j).2 _ hz
  have hK : S.spanTo g j ≤ LinearMap.ker (FramePsi.pairL L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    change hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg]
    rintro rfl
    simp at hi
  have h2 := LinearMap.mem_ker.1 (hK hB)

  rw [← e', map_sub, map_sum, sub_eq_zero] at h2
  have h3 : ∀ i, FramePsi.pairL L S.Hm (gs j) (al i • g i) = if i = j.castSucc then al i else 0 := by
    intro i
    rw [map_smul]
    change al i * hf L S.Hm (g i) (gs j) = _
    rw [hd]
    split_ifs <;> simp
  simp only [h3, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  exact h2

theorem psi'_eq_one (n : S.GLV) (hn : ∀ v ∈ perp L S.Hm S.X', n v = v) : S.psi' n = 1 := by
  have h : ∀ j, S.coef S.f' S.es' n j = 0 := by
    intro j
    have hp : S.f' j.succ ∈ perp L S.Hm S.X' := by
      refine FramePsi.hf_span_right L S.Hm _ _ ?_
      rintro _ ⟨i, hi, rfl⟩
      rw [S.gram', if_neg]
      rintro ⟨-, rfl⟩
      simp at hi
    rw [Frames.coef, hn _ hp, Frames.h, S.dual', if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [Frames.psi', Frames.psiOf, h]

theorem perp_left {A B : Submodule E S.V} {u : S.V} (hu : u ∈ perp L S.Hm (A ⊔ B)) :
    u ∈ perp L S.Hm A := fun y hy => hu y (Submodule.mem_sup_left hy)

theorem perp_right {A B : Submodule E S.V} {u : S.V} (hu : u ∈ perp L S.Hm (A ⊔ B)) :
    u ∈ perp L S.Hm B := fun y hy => hu y (Submodule.mem_sup_right hy)

end

theorem move_term : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∃ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s ∧ S.IsTerm d Λ₁ ∧ S.moved Λ₁ x (-u) (L.cj s) = Λ ∧ (S.InFF β (j + 1) βJ d Λ₁ → S.IsMove (j + 1) d Λ₁ x x' (-u) (L.cj s)) ∧ ∀ al al' : Fin (r + 1) → E, x = ∑ i, al i • S.fr d Λ i → x' = ∑ i, al' i • S.fr' d Λ i → S.om d Λ₁ = S.om d Λ * L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ) u)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨n₀, hn₀, n₀', hn₀', n'', hn'', e₀, e₀i, e₀', f'', hset, hW⟩ :=
    GlobalTheory.T.move_lattice_isTerm_same_datum_with_witnesses L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨t1, t2, -, -, -, -, -, hux, -, -, -⟩ := GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨hT₁, hY⟩ := GlobalTheory.T.hermitianMove_preserves_frameLattice_levels L r k S j β βJ d Λ hT hFF x x' u s hM _ hset
  obtain ⟨hx, hx', hth, hlev, hu, hup, ⟨c, hc, hsc⟩, hs⟩ := hM
  have hb : x + x' ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1) := Submodule.add_mem_sup hx hx'
  have hmem : ∀ v, v ∈ (n₀⁻¹ • Λ : Submodule L.O S.V) ↔ eich L S.Hm x u s v ∈ Λ := fun v =>
    Set.ext_iff.1 hset v
  refine ⟨n₀⁻¹ • Λ, hset, hT₁, ?_, fun _ => ⟨hx, hx', ?_, ?_, ?_, (perp L S.Hm _).neg_mem hup, ?_, ?_⟩,
    fun al al' ex ex' => ?_⟩
  · ext v
    change eich L S.Hm x (-u) (L.cj s) v ∈ (n₀⁻¹ • Λ : Submodule L.O S.V) ↔ v ∈ Λ
    rw [hmem, ← e₀, ← e₀i]
    rw [show n₀ (n₀⁻¹ v) = v from n₀.apply_symm_apply v]
  · obtain ⟨y, hy, e⟩ := hth
    refine ⟨y, (hY y ?_).1 hy, e⟩
    have : y = algebraMap F E S.th⁻¹ • (x + x') := by
      rw [e, smul_smul, WitIndep.th_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hb
  · rw [(hY _ hb).2.2, hlev]
  · refine Submodule.neg_mem _ ((hmem u).2 ?_)
    have : eich L S.Hm x u s u = u + s • x + L.cj s • x := by
      have h1 : hf L S.Hm u x = 0 := hux
      have h2 : hf L S.Hm u u = s + L.cj s := hs.symm
      rw [eich, h1, h2]
      module
    rw [this]
    exact Λ.add_mem (Λ.add_mem hu t1) t2
  · exact ⟨L.cj c, cj_mem_O hc, by rw [hsc, map_mul, AlgEquiv.commutes]⟩
  · rw [L.cj_cj, Frames.h, hf_neg_l, hf_neg_r, neg_neg, add_comm]
    exact hs
  · have K := (TermBasic.term_basic L r k S d Λ hT).2.1
    have hw := K.2.2.1
    have hw' := K.2.2.2.1
    obtain ⟨p1, p2, p3, p4⟩ := FramePsi.psi_unitary_character L r k S
    obtain ⟨m, -, em, -, -, pm⟩ := EichlerUnip.eichler_mem_unip L r k S S.f S.es (.inl ⟨rfl, rfl⟩) j x u s
      hx (perp_left S hup) hs
    obtain ⟨m', -, em', -, -, pm'⟩ := EichlerUnip.eichler_mem_unip L r k S S.f' S.es' (.inr ⟨rfl, rfl⟩)
      j x' u s hx' (perp_right S hup) hs
    obtain rfl : m = n₀ := LinearEquiv.ext fun v => (em v).trans (e₀ v).symm
    obtain rfl : m' = n₀' := LinearEquiv.ext fun v => (em' v).trans (e₀' v).symm
    have q := pm _ hw
    have q' := pm' _ hw'
    rw [top_coord S S.f S.es S.dual _ hw j x hx al ex] at q
    rw [top_coord S S.f' S.es' S.dual' _ hw' j x' hx' al' ex'] at q'
    have a1 := p1 m hn₀ _ (mul_mem (inv_mem hn₀) hw)
    rw [mul_inv_cancel_left] at a1
    have a2 := p2 _ (mul_mem hn'' hn₀') _ hw'
    rw [p2 _ hn'' _ hn₀', psi'_eq_one S n'' f'', one_mul] at a2
    have z1 : S.psi m ≠ 0 := fun h => by simpa [h] using (p3 m).1
    have z2 : S.psi' m' ≠ 0 := fun h => by simpa [h] using (p3 m').2
    have hchi : L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ +
        al' j.castSucc • S.fr' d Λ j.succ) u)) = (S.psi m * S.psi' m')⁻¹ := by
      rw [AddChar.map_neg_eq_inv]
      congr 1
      change _ = S.psiOf S.f S.es m * S.psiOf S.f' S.es' m'
      rw [q, q', ← AddChar.map_add_eq_mul, Frames.h, hf_add_l, hf_smul_l, hf_smul_l, mul_add]
      rfl
    rw [(WitIndep.witness_independence L r k S _ _ _ _ hW).1, hchi, a2, Frames.om, a1]
    field_simp

end GlobalTheory.HL.MoveTerm
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselAmplitude_eq_smul_of_rescaled_stabilizerHaar : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (ψ ψ' : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (cN : ℝ), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsURepOn (UWset k r z) π → IsURepOn (UWset k r z') π' → (∀ n ∈ Nset k r, ‖ψ n‖ = 1 ∧ ‖ψ' n‖ = 1) → IsSPsiEquiv z ψ π Φ → IsSPsiEquiv z' ψ' π' Φ' → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → ∀ (γ : Mat k r) (μG μR ν ν' : Measure (Mt k r)) (t : ℝ), γ ∈ GG k r → (∀ ρ ∈ Rset k r γ, ψ (γ * ρ * γ⁻¹) = ψ' ρ) → IsHaarOn (GG k r) μG → IsHaarOn (Rset k r γ) μR → 0 < t → IsQuotMeas μG μR ν → IsQuotMeas μG (ENNReal.ofReal t • μR) ν' → ampJ ν cN Φ Φ' γ = (t : ℂ) • ampJ ν' cN Φ Φ' γ := by
  first | exact @GlobalTheory.SnMass.AmpUniq.amp_uniq | exact GlobalTheory.SnMass.AmpUniq.amp_uniq | (intros; apply GlobalTheory.SnMass.AmpUniq.amp_uniq <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.SgInf

theorem prod_integrand_integrable : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v (Matrix.of p.2 * Matrix.of p.1)) * ⟪PiS (psiGen k r z c) π (Matrix.of p.2)⁻¹ ξ, ξ⟫_ℂ) (μG.prod μS) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have hF := GlobalTheory.T.besselForm_coeff_product_fubini_integrable k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv v hv
  obtain ⟨hz, hT, hπ, hHaarS, _⟩ := hSide
  have : SigmaFinite μS := hHaarS.1
  have : SigmaFinite μG := hStd.2.2.2.2.1.1
  obtain ⟨-, -, hPiB, hPiC, -⟩ := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  have hS : IsClosedSub k r (Sset k r z) := (closedSub_groups k r z hz hT).2.2.2.1

  set T : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∈ Sset k r z} with hTdef
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hTm : MeasurableSet T := (hS.2.1.preimage hof).measurableSet
  have haeT : ∀ᵐ x ∂μS, x ∈ T := ae_iff.2 hHaarS.2.2.1

  have hinv : ContinuousOn (fun x : Mt k r => (Matrix.of x : Mat k r)⁻¹) T := by
    intro x hx
    have hg : (Matrix.of x : Mat k r)ᴴ * Hpk k r * (Matrix.of x : Mat k r) = Hpk k r := hS.1 hx
    have hH := Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r
    have hdet : IsUnit (Matrix.of x : Mat k r).det := by
      rw [isUnit_iff_ne_zero]
      intro h0
      have h1 := congrArg Matrix.det hg
      rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
      exact hH.ne_zero h1.symm
    have hc : ContinuousAt Ring.inverse (Matrix.of x : Mat k r).det := by
      simpa using NormedRing.inverse_continuousAt hdet.unit
    exact ((continuousAt_matrix_inv _ hc).comp hof.continuousAt).continuousWithinAt
  have hmaps : Set.MapsTo (fun x : Mt k r => (Matrix.of x : Mat k r)⁻¹) T (Sset k r z) :=
    fun x hx => hS.2.2.2.2 _ hx
  have hgc : ContinuousOn
      (fun x : Mt k r => ⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ) T :=
    ((hPiC.comp hinv hmaps).clm_apply continuousOn_const).inner continuousOn_const
  have hgm : AEStronglyMeasurable
      (fun x : Mt k r => ⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ) μS := by
    have h1 := hgc.aestronglyMeasurable (μ := μS) hTm
    rwa [Measure.restrict_eq_self_of_ae_mem haeT] at h1

  have hbd : ∀ x ∈ T,
      ‖⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ‖ ≤ ‖ξ‖ * ‖ξ‖ := by
    intro x hx
    have h1 := (hPiB _ (hmaps hx)).1
    calc _ ≤ ‖PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ‖ * ‖ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ξ‖ * ‖ξ‖ := by
        gcongr
        calc _ ≤ ‖PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹‖ * ‖ξ‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖ξ‖ := by gcongr
          _ = ‖ξ‖ := one_mul _
  have haeP : ∀ᵐ p ∂(μG.prod μS), p.2 ∈ T := by
    rw [ae_iff]
    have h1 : {p : Mt k r × Mt k r | ¬ p.2 ∈ T} = Set.univ ×ˢ {x | ¬ x ∈ T} := by
      ext p; simp
    rw [h1, Measure.prod_prod, ae_iff.1 haeT, mul_zero]
  refine hF.mul_bdd (c := ‖ξ‖ * ‖ξ‖)
    (hgm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd) ?_
  filter_upwards [haeP] with p hp
  exact hbd p.2 hp

end GlobalTheory.SgInf
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselRegularDoubleCoset_polynomial_properness : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', max (opn s) (opn s') ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  first | exact @GlobalTheory.SgInf.PolyProper.poly_proper | exact GlobalTheory.SgInf.PolyProper.poly_proper | (intros; apply GlobalTheory.SgInf.PolyProper.poly_proper <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_continuous_limit_uniformCauchy : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp] (f : ℕ → Mat k r → Wp) (g : Mt k r → Wp), (∀ j, ContinuousOn (f j) (GG k r)) → (∀ Q : Set (Mt k r), IsCompact Q → AEStronglyMeasurable g (μ.restrict Q)) → (∀ Q : Set (Mt k r), IsCompact Q → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N, ∀ x ∈ Q, Matrix.of x ∈ GG k r → ‖f j (Matrix.of x) - f l (Matrix.of x)‖ ≤ ε) → (∀ Q : Set (Mt k r), IsCompact Q → Filter.Tendsto (fun j : ℕ => ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0)) → ∃ F : Mat k r → Wp, ContinuousOn F (GG k r) ∧ ((fun x : Mt k r => F (Matrix.of x)) =ᵐ[μ] g) ∧ ∀ x ∈ GG k r, Filter.Tendsto (fun j : ℕ => f j x) Filter.atTop (nhds (F x)) := by
  first | exact @GlobalTheory.SgInf.RegLimit.exists_continuous_limit | exact GlobalTheory.SgInf.RegLimit.exists_continuous_limit | (intros; apply GlobalTheory.SgInf.RegLimit.exists_continuous_limit <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.sobolev_ineq_translate_compact : ∀ (k r : ℕ) (μ : Measure (Mt k r)) (C₀ : ℝ) (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsHaarOn (GG k r) μ → IsCompact K₀ → (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C₀ * (Ws.map fun ws => ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μ).sum) → ∀ Q : Set (Mt k r), IsCompact Q → ∃ K₂ : Set (Mt k r), IsCompact K₂ ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → (∀ ws ∈ Ws, ContinuousOn (rdWord ws f) (GG k r)) → ∀ x ∈ Q, Matrix.of x ∈ GG k r → ENNReal.ofReal (‖f (Matrix.of x)‖ ^ 2) ≤ ENNReal.ofReal |C₀| * (Ws.map fun ws => ∫⁻ y in K₂, (‖rdWord ws f (Matrix.of y)‖₊ : ENNReal) ^ 2 ∂μ).sum := by
  first | exact @GlobalTheory.SgInf.SobTranslate.sobolev_translate | exact GlobalTheory.SgInf.SobTranslate.sobolev_translate | (intros; apply GlobalTheory.SgInf.SobTranslate.sobolev_translate <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_isFolnerSequenceBessel : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μS : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (Sset k r z) μS → ∃ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om := by
  first | exact @GlobalTheory.SgInf.FolnerSets.exists_isFolner | exact GlobalTheory.SgInf.FolnerSets.exists_isFolner | (intros; apply GlobalTheory.SgInf.FolnerSets.exists_isFolner <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem exists_isQuotMeas_Sset : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μG μS : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (GG k r) μG → IsHaarOn (Sset k r z) μS → ∃ ν : Measure (Mt k r), IsQuotMeas μG μS ν := by
  intro k r z μG μS hz hT hG hS
  obtain ⟨μW, hW⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  obtain ⟨μN, hN⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  have conv : ∀ {U : Set (Mat k r)} {μ : Measure (Mt k r)}, Formalism.FourierDecayAlt.B.IsHaarOn U μ → IsHaarOn U μ := by
    intro U μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩
  obtain ⟨hSg, hsub, hH, hR⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT
    (conv hW) (conv hN)
  have hS' : PI.IsHaarOnM (Sset k r z) μS := hS
  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ _ hSg hH).1 μS hS'
  have hR' : PI.IsRightInvM (Sset k r z) μS := by
    intro s hs
    rw [hc, Measure.map_smul, hR s hs]
    exact (GlobalTheory.ProdHaar.measurable_rmulQ s).aemeasurable
  obtain ⟨hGg, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  exact GlobalTheory.QuotWeil.exists_isQuotM _ _ _ μG μS hGg hSg hsub (hGH μG hG).1 hS' hR'

end GlobalTheory.SgInf
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.ballVol_succ_sq_eq_pow_mul_prod : ∀ (P Q : ℕ) (r : ℝ), 0 < r → ballVol ((P + Q + 1) ^ 2) r = (2 : ℝ≥0∞) ^ (P + Q) * ((volume : Measure (ℝ × Sp P Q)).prod (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))) {p | tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} := by
  first | exact @GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq | exact GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq | (intros; apply GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq <;> assumption)
end
