module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle893
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle636
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

open KaehlerDifferential DividedPowers GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm

namespace GlobalTheory.SmoothLift

private theorem crystallineSmoothLift_natural_local :
    ∃ e₁ : ∀ D : Data, CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s,
      ∀ (D D' : Data) (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (h : φ ≫ D.s = D'.s ≫ spMap σ)
        (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c,
        IsPull1 h (e₁ D c) (e₁ D' (m.pull1 c)) := by
  let Λ : ∀ D : Data, Lift D := fun D ↦ Classical.choice (GlobalTheory.T.nonempty_smoothLiftAffineThickenings D)
  obtain ⟨hr1, -⟩ := GlobalTheory.T.crystallineCechDeRham_relations_total_detect_zero
  have E1 : ∀ D : Data, ∃ e : CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s, ∀ c h, e c = h ↔ (Λ D).Rel1 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr1 D (Λ D)).1 (hr1 D (Λ D)).2.1 (hr1 D (Λ D)).2.2
      (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).1 (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.1
  choose e₁ he₁ using E1
  refine ⟨e₁, ?_⟩
  intro D D' σ φ φ₀ h m hc c
  exact GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism.1 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _
    ((he₁ D c _).1 rfl) ((he₁ D' _ _).1 rfl)

end GlobalTheory.SmoothLift

namespace GlobalTheory.CrysFlatBC

open GlobalTheory.SmoothLift

theorem bijective_liftSemi_pull1 : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] [Module.Flat R D] (π : D →+* R) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : R, π (algebraMap R D a) = a) → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (t : X ⟶ Sp D) (φ : X ⟶ X), Smooth s → IsSeparated s → QuasiCompact s → t = s ≫ spMap π → φ = 𝟙 X → ∀ m : IsMor (dp0 R) s κ t (algebraMap R D) φ, Function.Bijective (liftSemi m.pull1) := by
  intro R D _ _ _ _ π κ hκ hπ X s t φ hs hs' hs'' ht hφ m
  subst hφ ht
  obtain ⟨e₁, n⟩ := GlobalTheory.SmoothLift.crystallineSmoothLift_natural_local
  have hb : spMap π ≫ spMap (algebraMap R D) = 𝟙 _ := by
    rw [← Cris.spMap_comp, show π.comp (algebraMap R D) = RingHom.id R from RingHom.ext hπ, Cris.spMap_id]
  obtain ⟨X', q, s', H⟩ : ∃ (X' : Scheme.{0}) (q : X' ⟶ X) (s' : X' ⟶ Sp D),
      IsPullback q s' s (spMap (algebraMap R D)) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  let i : X ⟶ X' := H.lift (𝟙 X) (s ≫ spMap π) (by rw [Category.assoc, hb]; simp)
  have hiq : i ≫ q = 𝟙 X := H.lift_fst _ _ _
  have his : i ≫ s' = s ≫ spMap π := H.lift_snd _ _ _
  have hp : IsPullback i s s' (spMap π) :=
    IsPullback.of_right (by rw [hiq, hb]; exact IsPullback.id_horiz s) his H
  have k1 : Smooth s' := MorphismProperty.of_isPullback (P := @Smooth) H hs
  have k2 : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) H hs'
  have k3 : QuasiCompact s' := MorphismProperty.of_isPullback (P := @QuasiCompact) H hs''
  let D₀ := Data.self s hs hs' hs''
  let D' := Data.ofQuot κ hκ π (fun a ↦ ⟨_, hπ a⟩) rfl s' s i k1 k2 k3 hp _ rfl
  have w : 𝟙 X ≫ 𝟙 X = i ≫ q := by rw [hiq, Category.id_comp]
  have key := n D₀ D' (algebraMap R D) q (𝟙 X) H.w m w
  obtain ⟨e, e', he⟩ : ∃ (e : Cris.H1 (dp0 R) s ≃ₗ[R] HH1 s) (e' : Cris.H1 κ (s ≫ spMap π) ≃ₗ[D] HH1 s'),
      ∀ c, IsPull1 H.w (e c) (e' (m.pull1 c)) := ⟨e₁ D₀, e₁ D', key⟩
  exact (GlobalTheory.T.liftBaseChange_bijective_linearEquiv_square_univ R D (Cris.H1 (dp0 R) s) (HH1 s) (Cris.H1 κ (s ≫ spMap π)) (HH1 s')
    e.toLinearMap e'.toLinearMap m.pull1 (pullHH1 H.w) e.bijective e'.bijective fun c ↦ (he c).eq_pullHH1).2
    (GlobalTheory.T.hyper_cohomology_flat_base_change R D X X' s s' q H hs' hs'')

end GlobalTheory.CrysFlatBC
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.BergRank

open ReciprocityTheory.ChartRestriction.G.FD

theorem statement_abs_wtOf_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (la : AllWt.Weight Dw) (x : (E →+* ℂ) × ℕ) :
    |(((wtOf Dw la 0).1 x : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  have key : ∀ τ i, |(la τ i : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := fun τ i =>
    (Finset.single_le_sum (f := fun i => |(la τ i : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun τ => ∑ i, |(la τ i : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have h0 : (0 : ℝ) ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold wtOf
  dsimp only
  split_ifs <;> push_cast <;> simp only [sub_zero, abs_neg, abs_zero] <;> first | exact h0 | exact key _ _

theorem statement_abs_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) (τ : (U.X k).Ψ) (i : Fin r) :
    |((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  unfold AllWt.modelWt
  have h2 : (wtOf Dw la 0).2 / 2 = 0 := by rw [AllWt.wtOf_snd]; simp
  split_ifs
  · rw [h2, add_zero]; exact statement_abs_wtOf_le la _
  · rw [h2, sub_zero]; push_cast; rw [abs_neg]; exact statement_abs_wtOf_le la _

theorem statement_sum_spread_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) :
    ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤
      2 * (Module.finrank ℚ E : ℝ) * ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  set S := ∑ τ, ∑ i, |(la τ i : ℝ)| with hS
  have h0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsp : ∀ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ 2 * S := by
    intro τ
    unfold Data.spread
    rcases isEmpty_or_nonempty (Fin r) with hr | hr
    · simp; linarith
    · have hb := fun i => abs_le.1 (statement_abs_modelWt_le U la k τ i)
      have h1 : (⨆ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)) ≤ S := ciSup_le fun i => (hb i).2
      have h2 : -S ≤ ⨅ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ) := le_ciInf fun i => (hb i).1
      linarith
  have hcard : (Fintype.card (U.X k).Ψ : ℝ) ≤ Module.finrank ℚ E := by
    have e1 : Fintype.card (U.X k).Ψ = (U.X k).Ψ.card := Fintype.card_coe _
    have e2 : (U.X k).Ψ.card ≤ Fintype.card (E →+* ℂ) := Finset.card_le_univ _
    rw [NumberField.Embeddings.card] at e2
    exact_mod_cast e1 ▸ e2
  calc ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ ∑ _τ : (U.X k).Ψ, 2 * S :=
        Finset.sum_le_sum fun τ _ => hsp τ
    _ = (Fintype.card (U.X k).Ψ : ℝ) * (2 * S) := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ (Module.finrank ℚ E : ℝ) * (2 * S) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = _ := by ring


end GlobalTheory.BergRank


theorem _root_.GlobalTheory.T.antitone_weight_log_bound : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 20 * Lb → ∀ Z, BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ SupBdWt Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ Real.log (Y.rkC la Z) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro hP
  refine ⟨4000, by norm_num, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hsz hfr ho la hla hS Z
  have hL := (GlobalTheory.T.deepLevelCover_principalLevel_laws_galois D T j Y e o hT hj hY hY.unit hY.modelW).1
  set S : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set n : ℝ := (Module.finrank ℚ D.host.E : ℝ) with hn
  have hn1 : 1 ≤ n := by
    have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    rw [hn]; exact_mod_cast this
  have hnlog : Real.log n ≤ 3 * Lb := (log_finrank_le_fieldSz _).trans hsz
  set w : ℝ := 2 * n * S + 1 with hw
  have hnS : 0 ≤ n * S := mul_nonneg (by linarith) hS0
  have hw1 : 1 ≤ w := by rw [hw]; nlinarith
  have hlogw : Real.log w ≤ 25 * Lb := by
    have hint : S = (((∑ τ, ∑ k, |la τ k|) : ℤ) : ℝ) := by rw [hSdef]; push_cast; rfl
    have hz : (0 : ℤ) ≤ ∑ τ, ∑ k, |la τ k| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    rcases hz.eq_or_lt with h0 | h1
    · have : S = 0 := by rw [hint, ← h0]; simp
      rw [hw, this]; simp; linarith
    · have hS1 : 1 ≤ S := by rw [hint]; exact_mod_cast h1
      have hwle : w ≤ 3 * (n * S) := by rw [hw]; nlinarith
      have hlS : Real.log S ≤ 20 * Lb := hS
      have e1 : Real.log w ≤ Real.log (3 * (n * S)) := Real.log_le_log (by linarith) hwle
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity)] at e1
      have h3 : Real.log 3 < 2 := by
        have := Real.log_two_lt_d9; have h4 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
        have : Real.log 4 = 2 * Real.log 2 := by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith
      linarith
  obtain ⟨hβ1, hβ⟩ := GlobalTheory.T.sup_constant_log_bound D Y.d.l₂.M Lb w (by have := Y.d.l₂.three_le; omega) hLb hM hsz hfr hw1 hlogw
  set β := GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d Y.d.l₂.M w with hβdef
  have hβexp : β ≤ Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3) := by
    rw [← Real.exp_log (by linarith : 0 < β)]; exact Real.exp_le_exp.2 hβ
  have hsp : ∀ σ k, ∑ τ, ((Y.U σ).X k).spread (AllWt.modelWt (Y.U σ) (wtOf _ la 0) k) τ ≤ w := fun σ k =>
    (GlobalTheory.BergRank.statement_sum_spread_modelWt_le _ la k).trans (by rw [hw]; linarith)
  have hB : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β := fun σ hσ y hy =>
    GlobalTheory.T.level_geometry_weight_bound hP.p6 D j _ _ _ _ _ Y.U Y.dict hL σ hσ (wtOf _ la 0) (AllWt.even_wtOf la 0) w (by linarith) (hsp σ) Z y hy
  have hBexp : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) :=
    fun σ hσ y hy => (hB σ hσ y hy).trans (ENNReal.ofReal_le_ofReal hβexp)
  refine ⟨hBexp, ?_, ?_⟩
  · refine SupBdWt.of_bergOn (Real.exp_pos _).le ?_ hBexp
    intro σ hσ g
    obtain ⟨th, hr, -, hd⟩ := hY.dictU σ hσ
    exact Formalism.L2.Pj.dict_dom_of hd g
  · have hrk := GlobalTheory.T.cuspFormRank_le_bergmanBound_goodCover D T.toCore j Y e o hY la Z β (by linarith) hB
    have hpos : 0 ≤ 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by positivity
    rcases (show (0 : ℝ) ≤ Y.rkC la Z by unfold Deep.rkC; positivity).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; exact hpos
    · exact (Real.log_le_log h0 hrk).trans hβ

end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SubGlue
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.LB (resG_resG resG_self exists_fun_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)

variable {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {L : LB X}

abbrev spanRes (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (k : L.ι) {W : X.Opens} (hk : W ≤ L.U k) :
    Submodule Γ(X, W) Γ(F, W) :=
  Submodule.span Γ(X, W) (Set.range fun i => resM F hk (s k i))

theorem resM_mem_spanRes (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) {k : L.ι} {W W' : X.Opens}
    (hW : W' ≤ W) (hk : W ≤ L.U k) {x : Γ(F, W)} (hx : x ∈ spanRes s k hk) :
    resM F hW x ∈ spanRes s k (hW.trans hk) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => resG X hW (c i), ?_⟩

  simp only [map_sum, resM_smul, resM_resM]

theorem spanRes_le (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (A : ∀ k k' : L.ι, Matrix (Fin r) (Fin r) Γ(X, L.U k ⊓ L.U k'))
    (hA : ∀ (k k' : L.ι) (i : Fin r), resM F (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (s k' i) =
      ∑ j, A k k' j i • resM F (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k) (s k j))
    (k k' : L.ι) {W : X.Opens} (hk : W ≤ L.U k) (hk' : W ≤ L.U k') :
    spanRes s k' hk' ≤ spanRes s k hk := by
  rw [spanRes, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have e := congrArg (resM F (le_inf hk hk')) (hA k k' i)

  simp only [resM_resM, map_sum, resM_smul] at e
  change resM F hk' (s k' i) ∈ spanRes s k hk
  rw [show resM F hk' (s k' i) = _ from e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

def IsLoc (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (V : X.Opens) (x : Γ(F, V)) : Prop :=
  ∀ p ∈ V, ∃ (k : L.ι) (W : X.Opens) (h : W ≤ V) (hk : W ≤ L.U k), p ∈ W ∧
    resM F h x ∈ spanRes s k hk

def sub (hL : L.IsLB) (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (hmono : ∀ (k k' : L.ι) (W : X.Opens) (hk : W ≤ L.U k) (hk' : W ≤ L.U k'),
      spanRes s k' hk' ≤ spanRes s k hk) : VB.Sub F where
  sec V :=
    { carrier := {x | IsLoc s V x}
      zero_mem' := fun p hp => by
        obtain ⟨k, hk⟩ := Semi.LB.mem_of_cover hL p
        exact ⟨k, V ⊓ L.U k, inf_le_left, inf_le_right, ⟨hp, hk⟩, by rw [map_zero]; exact zero_mem _⟩
      add_mem' := fun {x y} hx hy p hp => by
        obtain ⟨k, W, h, hk, hpW, hxW⟩ := hx p hp
        obtain ⟨k', W', h', hk', hpW', hyW'⟩ := hy p hp
        refine ⟨k, W ⊓ W', inf_le_left.trans h, inf_le_left.trans hk, ⟨hpW, hpW'⟩, ?_⟩
        rw [map_add (f := _)]
        refine add_mem ?_ (hmono k k' _ (inf_le_left.trans hk) (inf_le_right.trans hk') ?_)
        · have := resM_mem_spanRes s (inf_le_left : W ⊓ W' ≤ W) hk hxW
          rw [resM_resM] at this
          exact this
        · have := resM_mem_spanRes s (inf_le_right : W ⊓ W' ≤ W') hk' hyW'
          rw [resM_resM] at this
          exact this
      smul_mem' := fun a x hx p hp => by
        obtain ⟨k, W, h, hk, hpW, hxW⟩ := hx p hp
        refine ⟨k, W, h, hk, hpW, ?_⟩
        rw [resM_smul]
        exact Submodule.smul_mem _ _ hxW }
  res_mem {V W} hWV x hx := fun p hp => by
    obtain ⟨k, W', h', hk, hp', hx'⟩ := (hx : IsLoc s V x) p (hWV hp)
    refine ⟨k, W ⊓ W', inf_le_left, inf_le_right.trans hk, ⟨hp, hp'⟩, ?_⟩
    rw [resM_resM]
    have := resM_mem_spanRes s (inf_le_right : W ⊓ W' ≤ W') hk hx'
    rw [resM_resM] at this
    exact this
  mem_of_local {V x} H := fun p hp => by
    obtain ⟨W, h, hpW, hW⟩ := H p hp
    obtain ⟨k, W', h', hk, hp', hx'⟩ := (hW : IsLoc s W _) p hpW
    refine ⟨k, W', h'.trans h, hk, hp', ?_⟩
    rw [resM_resM] at hx'
    exact hx'

theorem mem_spanRes_of_mem (hL : L.IsLB) (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (hmono : ∀ (k k' : L.ι) (W : X.Opens) (hk : W ≤ L.U k) (hk' : W ≤ L.U k'),
      spanRes s k' hk' ≤ spanRes s k hk)
    (hli : ∀ (k : L.ι) (V : X.Opens) (h : V ≤ L.U k),
      LinearIndependent Γ(X, V) fun i => resM F h (s k i))
    {k : L.ι} {V : X.Opens} (hV : V ≤ L.U k) {x : Γ(F, V)}
    (hx : x ∈ (sub hL s hmono).sec V) : x ∈ spanRes s k hV := by
  have hx' : IsLoc s V x := hx
  choose k' W hW hk' hpW hxW using fun p : V => hx' p p.2
  have hc : V ≤ iSup W := fun p hp => Opens.mem_iSup.2 ⟨⟨p, hp⟩, hpW _⟩
  have hin (p : V) : resM F (hW p) x ∈ spanRes s k ((hW p).trans hV) :=
    hmono k (k' p) _ _ _ (hxW p)
  choose c hc' using fun p => (Submodule.mem_span_range_iff_exists_fun _).1 (hin p)
  have key (p q : V) (i : Fin r) : resG X (inf_le_left : W p ⊓ W q ≤ W p) (c p i) =
      resG X (inf_le_right : W p ⊓ W q ≤ W q) (c q i) := by
    have hl := hli k (W p ⊓ W q) (inf_le_left.trans ((hW p).trans hV))
    have e1 := congrArg (resM F (inf_le_left : W p ⊓ W q ≤ W p)) (hc' p)
    have e2 := congrArg (resM F (inf_le_right : W p ⊓ W q ≤ W q)) (hc' q)

    simp only [map_sum, resM_smul, resM_resM] at e1 e2
    exact Fintype.linearIndependent_iffₛ.1 hl _ _ (e1.trans e2.symm) i
  choose b hb using fun i => exists_fun_of_cover W hW hc (fun p => c p i) fun p q => key p q i
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨b, ?_⟩
  refine sec_ext_of_cover W hW hc fun p => ?_

  simp only [map_sum, resM_smul, resM_resM, hb]
  exact hc' p

end GlobalTheory.SubGlue

namespace GlobalTheory.SubGlue
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)

theorem exists_sub_isVB_lbIso_det : ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ) (L : LB X), L.IsLB → ∀ (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (A : ∀ k k' : L.ι, Matrix (Fin r) (Fin r) Γ(X, L.U k ⊓ L.U k')), (∀ (k : L.ι) (V : X.Opens) (h : V ≤ L.U k), LinearIndependent Γ(X, V) fun i => GlobalTheory.Twist.resM F h (s k i)) → (∀ (k k' : L.ι) (i : Fin r), GlobalTheory.Twist.resM F (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (s k' i) = ∑ j, A k k' j i • GlobalTheory.Twist.resM F (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k) (s k j)) → (∀ k k' : L.ι, (L.g k k').val = (A k k').det) → ∃ (W : X.Modules) (ι : W ⟶ F), Mono ι ∧ GlobalTheory.VB.IsVB W r ∧ LBIso L (GlobalTheory.VB.det W r) := by
  intro X F r L hL s A hli hA hdet
  have hmono := spanRes_le s A hA
  let N := sub hL s hmono
  have hmem (k : L.ι) (i : Fin r) : s k i ∈ N.sec (L.U k) := fun p hp =>
    ⟨k, L.U k, le_rfl, le_rfl, hp, Submodule.subset_span ⟨i, rfl⟩⟩
  have hfr (k : L.ι) : VB.IsFrame fun i => N.mkSec (s k i) (hmem k i) :=
    GlobalTheory.EigenFrames.isFrame_mkSec N (s k) (hmem k) (hli k)
      fun V h x hx => mem_spanRes_of_mem hL s hmono hli h hx
  have hv (k k' : L.ι) (i : Fin r) :
      resM N.toMod (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (N.mkSec (s k' i) (hmem k' i)) =
        ((hfr k).basis (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k)).equivFun.symm
          fun j => A k k' j i := by
    rw [VB.IsFrame.basis_equivFun_symm]
    apply N.incl_app_injective
    rw [app_resM, VB.Sub.incl_app_mkSec, hA]

    rw [← appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, appLinear_apply, app_resM, VB.Sub.incl_app_mkSec]
  refine ⟨N.toMod, N.incl, inferInstance, ?_⟩
  refine VB.lbIso_det_of_frames hL _ hfr fun k k' => Units.ext ?_
  rw [hdet, VB.IsFrame.val_detUnit, Module.Basis.det_apply]
  congr 1
  ext a b
  rw [Module.Basis.toMatrix_apply, hv, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.SubGlue
end
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagMod.Frames

theorem lies_of_chart_tri : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (F : Frames Y π), F.TopEigen → ∀ (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (z : Sp S ⟶ Z) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hx : z ≫ π = frX P ≫ Y.j) (U : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ σ, (U σ).BlockTriangular id) → (∀ σ i, IsUnit (U σ i i)) → (∀ σ i, frVec Y P rfl σ i = ∑ j, U σ j i • F.vecAt k z hz hx σ j) → F.Lies z P := by
  intro E _ _ _ H Dw l Xo c O _ β Y Z π F hT S _ _ P z k hz hx U hU hd hv
  obtain ⟨Q, hQ⟩ := hT.exists_chartFr (frX_snd P) hx k hz
  have hQx : frX Q ≫ Y.j = frX P ≫ Y.j := hQ.over.trans hx
  have hv' : ∀ σ i, frVec Y P rfl σ i = ∑ j, U σ j i • frVec Y Q hQx σ j := fun σ i => by
    rw [hQ.frVec_eq hx hQx]; exact hv σ i
  have e : P.x = Q.x := by
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd P) (frX_snd Q) hQx.symm]
  have hB : ∃ t, FrBor t Q P := by
    have hM := F.inM hz hx
    clear hv hQ
    revert hv' hQx hM
    obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P
    dsimp only at e
    subst e
    intro hQx hv' hM
    obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
    exact ⟨_, frBor_of_frVec hM hQx rfl
      (fun ix => match ix with | none => u0 | some p => (hd p.1 p.2).unit) U hU (fun _ _ => rfl) hv' fun _ => hu0⟩
  obtain ⟨t, ht⟩ := hB
  exact hQ.lies.frBor ht

end GlobalTheory.FlagMod.Frames
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

theorem mulVec_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.St β)
    (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hv : v ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
  GlobalTheory.T.frameStabiliser_mapsTo_completedLattice β Λ hβ x hx v hv

theorem mulVec_mem_hat (D : D7) {n : ℕ} (β : GL (Fin n) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (k : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hk : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k ∈ Formalism.L2.DIV.St β)
    (x : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) (hx : x ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E))) :
    k.1 *ᵥ x ∈
      GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  have h1 := GlobalTheory.PrincInLevel.swap_mem_hatL Λ x hx
  have h2 := mulVec_mem_hatL β Λ hβ _ hk _ h1
  have h3 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h2
  convert h3 using 1
  ext i
  simp [Formalism.UG.bc, Formalism.IndefR.Lev.swapAE, Matrix.mulVec, dotProduct,
    RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul]

end GlobalTheory.MassLinkConj

namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

end GlobalTheory.MassLinkConj

namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix


end GlobalTheory.MassLinkConj
end
end
