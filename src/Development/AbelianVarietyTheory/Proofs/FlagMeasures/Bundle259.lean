module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.FiniteDimensionalOfOrtho
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle102
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle237
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle251
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.JPMemAwayP
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle248
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle249
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle239
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle246
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle047
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle250
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011

@[expose] public section

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.StdMass


open NumberField Matrix in
open scoped ENNReal Classical in
theorem _root_.GlobalTheory.Mass.StdMass.isSymm_of_ortho {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ} (hL : _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    h.IsSymm := by
  unfold _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice at hL
  obtain ⟨e, -, hspan, -, horth⟩ := hL
  refine LinearMap.IsSymm.mk fun x y => ?_
  obtain ⟨c, rfl⟩ := _root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.exists_coord hspan x
  obtain ⟨d, rfl⟩ := _root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.exists_coord hspan y
  rw [_root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.form_sum horth, _root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.form_sum horth]

  simp only [map_sum, starRingEnd_apply, star_mul, star_star]

open NumberField Matrix in
open scoped ENNReal Classical in
private theorem massU_zero_eq_one (K : Type) [Field K] [NumberField K] [StarRing K] :
    _root_.Formalism.MainNotions.S.Cnt.massU K 0 = 1 := by
  have hsub : ∀ M N : Submodule (𝓞 K) (Fin 0 → K), M = N := fun M N => Subsingleton.elim M N
  haveI : Subsingleton ((Fin 0 → K) ≃ₗ[K] (Fin 0 → K)) :=
    ⟨fun f g => LinearEquiv.ext fun x => Subsingleton.elim _ _⟩
  have hlat : Submodule.IsLattice K (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) := _root_.ReciprocityTheory.ChartRestriction.L3.isLattice_of_ortho (_root_.Formalism.MainNotions.StandardLattice.stdLat_ortho K 0)
  have hfull : Submodule.IsFullLattice K (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) :=
    { toIsLattice := hlat, span_eq_top := Subsingleton.elim _ _ }
  have hgen : _root_.Formalism.MainNotions.S.Cnt.stdLat K 0 ∈ _root_.Formalism.HermitianLatticesTheory.genus (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) := by
    unfold _root_.Formalism.HermitianLatticesTheory.genus _root_.Formalism.HermitianLatticesTheory.SameGenus
    exact ⟨hfull, fun p _ => ⟨1, one_mem _, hsub _ _⟩⟩
  have hs : ∃ s, _root_.Formalism.ThetaLiftIndependence.IsClassReps (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) s := by
    refine ⟨{_root_.Formalism.MainNotions.S.Cnt.stdLat K 0}, ?_⟩
    unfold _root_.Formalism.ThetaLiftIndependence.IsClassReps
    refine ⟨fun M hM => ?_, fun M _ => ⟨_root_.Formalism.MainNotions.S.Cnt.stdLat K 0,
      ⟨Finset.mem_singleton_self _, 1, one_mem _, hsub _ _⟩,
      fun N hN => Finset.mem_singleton.mp hN.1⟩⟩
    rw [Finset.mem_singleton.mp hM]
    exact hgen
  have hchoose : hs.choose = {_root_.Formalism.MainNotions.S.Cnt.stdLat K 0} := by
    have hspec := hs.choose_spec
    unfold _root_.Formalism.ThetaLiftIndependence.IsClassReps at hspec
    obtain ⟨N, ⟨hN, -⟩, -⟩ := hspec.2 _ hgen
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨?_, fun M _ => hsub _ _⟩
    have hN' : N = _root_.Formalism.MainNotions.S.Cnt.stdLat K 0 := hsub _ _
    exact hN' ▸ hN
  have hcard : Nat.card (_root_.Formalism.ThetaLiftIndependence.autL (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨inferInstance, ⟨⟨1, ?_⟩⟩⟩
    unfold _root_.Formalism.ThetaLiftIndependence.autL
    exact ⟨one_mem _, hsub _ _⟩
  unfold _root_.Formalism.MainNotions.S.Cnt.massU
  rw [_root_.Formalism.HermitianLatticesTheory.massBasic_mass_eq _ _ hs, hchoose, Finset.sum_singleton, hcard]
  norm_num


open NumberField Matrix in
open scoped ENNReal Classical in
theorem _root_.GlobalTheory.Mass.StdMass.main : ∀ (K : Type) [Field K] [NumberField K]
    [StarRing K], _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ j : ℕ, (_root_.Formalism.MainNotions.S.Cnt.stdH K j).IsSymm ∧
      _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice (_root_.Formalism.MainNotions.S.Cnt.stdH K j) (_root_.Formalism.MainNotions.S.Cnt.stdLat K j) j ∧ 0 < _root_.Formalism.MainNotions.S.Cnt.massU K j ∧ _root_.Formalism.MainNotions.S.Cnt.massU K 0 = 1 ∧
      ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
        (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h L j →
        _root_.Formalism.HermitianLatticesTheory.mass h L = _root_.Formalism.MainNotions.S.Cnt.massU K j ∧ _root_.GlobalTheory.Mass.PD h := by
  intro K _ _ _ hK j
  have hsymm : (_root_.Formalism.MainNotions.S.Cnt.stdH K j).IsSymm := _root_.ReciprocityTheory.ChartRestriction.L3.stdForm_isSymm K j
  have hortho : _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice (_root_.Formalism.MainNotions.S.Cnt.stdH K j) (_root_.Formalism.MainNotions.S.Cnt.stdLat K j) j := _root_.Formalism.MainNotions.StandardLattice.stdLat_ortho K j
  refine ⟨hsymm, hortho, ?_, massU_zero_eq_one K, fun V _ _ _ _ h L hL => ⟨?_, ?_⟩⟩
  · unfold _root_.Formalism.MainNotions.S.Cnt.massU
    exact _root_.ReciprocityTheory.ChartRestriction.L3.mass_pos_of_ortho hK hsymm hortho
  · exact (_root_.Formalism.MainNotions.StandardLattice.mass_ortho K hK j V h L hL).trans rfl
  · have hpos := _root_.ReciprocityTheory.ChartRestriction.L3.isTotPosDef_of_ortho hK (_root_.GlobalTheory.Mass.StdMass.isSymm_of_ortho hL) hL
    unfold _root_.ReciprocityTheory.ChartRestriction.L3.IsTotPosDef at hpos
    unfold _root_.GlobalTheory.Mass.PD
    exact fun τ x hx => hpos x hx τ

end GlobalTheory.Mass.StdMass
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordSq


open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.CoordSq.sums_eq : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ)
    (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k) (c : _root_.GlobalTheory.HL.Coord P S),
    ∀ (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d0 : _root_.Formalism.MainNotions.S.LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (_root_.Formalism.MainNotions.S.LocNG.BBne (H := H))
        = ENNReal.ofReal κ * S.ampSq (fun d Λ => ¬ S.BBzero d Λ) ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (fun t => ¬ _root_.Formalism.MainNotions.S.LocNG.BBne (H := H) t)
        = ENNReal.ofReal κ * S.ampSq S.BBzero ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (fun _ => True) = ENNReal.ofReal κ * S.ampSq (fun _ _ => True) ∧
      _root_.Formalism.MainNotions.S.LocNG.nn R d0 = ENNReal.ofReal κ * S.nn := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d0
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨κ, hκ, hsum⟩ := _root_.GlobalTheory.HL.CoordSum.tsum_reps_eq M hM H r k P S c R d0
  have hamp := _root_.GlobalTheory.HL.CoordAmp.amp_mass_eq M hM H r k P S c R
  have hvanA : ∀ (δ : S.Datum) (Q : Submodule M.L.O S.V → Prop),
      (¬ ∃ Λ, S.IsTerm δ Λ) → S.amp δ Q = 0 := by
    intro δ Q hδ
    unfold _root_.GlobalTheory.HL.Frames.amp
    refine (tsum_congr fun o => ?_).trans tsum_zero
    rw [if_neg fun h => hδ ⟨_, h.1⟩]
  have hvanM : ∀ (δ : S.Datum) (Q : Submodule M.L.O S.V → Prop),
      (¬ ∃ Λ, S.IsTerm δ Λ) → S.mass δ Q = 0 := by
    intro δ Q hδ
    unfold _root_.GlobalTheory.HL.Frames.mass
    refine (tsum_congr fun o => ?_).trans tsum_zero
    rw [if_neg fun h => hδ ⟨_, h.1⟩]
  have hinv : ∀ h ∈ S.H0, ∀ (δ : S.Datum) (Q : S.Datum → Submodule M.L.O S.V → Prop),
      (∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ → Q δ' Λ → Q δ' (s • Λ)) →
      (∀ δ' Λ, S.IsTerm δ' Λ → (Q δ' Λ ↔ Q (h • δ') (h • Λ))) →
      S.amp (h • δ) (Q (h • δ)) = S.amp δ (Q δ) ∧
        S.mass (h • δ) (Q (h • δ)) = S.mass δ (Q δ) :=
    fun h hh δ Q h1 h2 => _root_.GlobalTheory.InvH.amp_mass_smul M.L r k S h hh δ (Q δ)
      (Q (h • δ)) (fun s hs Λ hΛ => h1 δ s hs Λ hΛ) (fun Λ hΛ => h2 δ Λ hΛ)
  have hBBst : ∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ →
      (S.BBzero δ' (s • Λ) ↔ S.BBzero δ' Λ) :=
    fun δ' s hs Λ hΛ =>
      (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S δ' Λ hΛ s hs).2.2.2.2.2.2.2.1
  have hBBh : ∀ h ∈ S.H0, ∀ δ' Λ, S.IsTerm δ' Λ →
      (S.BBzero δ' Λ ↔ S.BBzero (h • δ') (h • Λ)) := by
    intro h hh δ' Λ hΛ
    obtain ⟨-, -, -, hM', hsat, -⟩ :=
      _root_.GlobalTheory.HL.ComplAct.main M.L r k S δ' Λ hΛ h hh
    unfold _root_.GlobalTheory.HL.Frames.BBzero
    rw [hM', hsat]
  have hsq : ∀ z : ℂ, ((‖z‖₊ : ℝ≥0∞) ^ 2) = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  have hA : ∀ (p : _root_.Formalism.MainNotions.S.Loc.Term V M r → Prop) (Q : S.Datum → Submodule M.L.O S.V → Prop),
      (∀ d, _root_.Formalism.MainNotions.S.LocNG.amp R d p
        = S.amp (c.dat d) (Q (c.dat d))) →
      (∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ → Q δ' Λ → Q δ' (s • Λ)) →
      (∀ h ∈ S.H0, ∀ δ' Λ, S.IsTerm δ' Λ → (Q δ' Λ ↔ Q (h • δ') (h • Λ))) →
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 p = ENNReal.ofReal κ * S.ampSq Q := by
    intro p Q hpQ h1 h2
    unfold _root_.Formalism.MainNotions.S.LocNG.sumSq _root_.GlobalTheory.HL.Frames.ampSq
    rw [← hsum (fun δ => ENNReal.ofReal (‖S.amp δ (Q δ)‖ ^ 2))
      (fun h hh δ => by rw [(hinv h hh δ Q h1 (h2 h hh)).1])
      (fun δ hδ => by rw [hvanA δ _ hδ, norm_zero]; simp)]
    refine tsum_congr fun d => ?_
    rw [hpQ, hsq]
  refine ⟨κ, hκ, ?_, ?_, ?_, ?_⟩
  · exact hA _ (fun δ Λ => ¬ S.BBzero δ Λ) (fun d => (hamp d).1)
      (fun δ' s hs Λ hΛ hq => by rwa [hBBst δ' s hs Λ hΛ])
      (fun h hh δ' Λ hΛ => not_congr (hBBh h hh δ' Λ hΛ))
  · exact hA _ S.BBzero (fun d => (hamp d).2.1)
      (fun δ' s hs Λ hΛ hq => (hBBst δ' s hs Λ hΛ).2 hq)
      (fun h hh δ' Λ hΛ => hBBh h hh δ' Λ hΛ)
  · exact hA _ (fun _ _ => True) (fun d => (hamp d).2.2.1)
      (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ => Iff.rfl)
  · unfold _root_.Formalism.MainNotions.S.LocNG.nn _root_.GlobalTheory.HL.Frames.nn
    rw [← hsum (fun δ => S.mass δ (fun _ => True))
      (fun h hh δ => (hinv h hh δ (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
        (fun _ _ _ => Iff.rfl)).2)
      (fun δ hδ => hvanM δ _ hδ)]
    refine tsum_congr fun d => ?_
    rw [(hamp d).2.2.2]

end GlobalTheory.HL.CoordSq
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem split_components :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E ⊗[F] v.adicCompletion F), y ∈ loc v L ↔ (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2) ∧ (∀ g : GL (Fin n) (v.adicCompletion F), ∃! h : UPts cm.sig J (v.adicCompletion F), bc ((RingHom.fst _ _).comp sp.toRingHom) h.1 = g) ∧ ∀ x y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x y)).1 = ∑ i, ∑ j, (sp (x i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet v sp hsig hdiag
  refine ⟨?_, ?_, ?_⟩
  · intro L y
    refine ⟨fun hy => ⟨⟨y, hy, fun _ => rfl⟩, y, hy, fun _ => rfl⟩, ?_⟩
    rintro ⟨⟨y₁, h₁, e₁⟩, y₂, h₂, e₂⟩
    have hint : ∀ x, x ∈ intV E v ↔
        (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
      split_integral_local F E v sp hdiag
    have ha : sp.symm (1, 0) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
    have hb : sp.symm (0, 1) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩
    have hm := (loc v L).add_mem ((loc v L).smul_mem ⟨_, ha⟩ h₁) ((loc v L).smul_mem ⟨_, hb⟩ h₂)
    have hy : y = (⟨_, ha⟩ : intV E v) • y₁ + (⟨_, hb⟩ : intV E v) • y₂ := by
      funext b
      apply sp.injective
      change sp (y b) = sp (sp.symm (1, 0) * y₁ b + sp.symm (0, 1) * y₂ b)
      rw [map_add (f := _), map_mul, map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      ext
      · simp [e₁ b]
      · simp [e₂ b]
    rw [hy]; exact hm
  · intro g
    obtain ⟨e, he⟩ := Formalism.L2.G.exists_locGL cm.sig J hJ (isUnit_iff_ne_zero.2 hdet) _ sp hsig
    refine ⟨e.symm g, ?_, fun h hh => ?_⟩
    · exact (he _).symm.trans (e.apply_symm_apply g)
    · rw [MulEquiv.eq_symm_apply]
      exact (he _).trans hh
  · intro x y
    unfold hR hform

    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl

end GlobalTheory.St.G
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePairNormalForm_invVol_top_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊔ N.R1) (N.Gam Λ ⊔ N.R1) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.invVol_top_layer_le | exact GlobalTheory.DegCnt.invVol_top_layer_le | (intros; apply GlobalTheory.DegCnt.invVol_top_layer_le <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.flagPairDefinitePartLattice_discriminant_eq_quotient : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → del H (flagPairDefinitePartLattice N.F N.F' Λ) = N.NT ∧ del H (flagPairDefinitePartLattice N.F' N.F Λ) = N.NT ∧ GenBy (dual H (flagPairDefinitePartLattice N.F N.F' Λ)) (flagPairDefinitePartLattice N.F N.F' Λ) 1 ∧ IsLatMod (flagPairDefinitePartLattice N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') ∧ IsLatMod (flagPairDefinitePartLattice N.F' N.F Λ) (wSp N.F N.F') (II N.F N.F') ∧ Nonempty ((↥(dual H (flagPairDefinitePartLattice N.F N.F' Λ)) ⧸ (flagPairDefinitePartLattice N.F N.F' Λ).comap (dual H (flagPairDefinitePartLattice N.F N.F' Λ)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(N.T : 𝓞 K)})) := by
  first | exact @GlobalTheory.DegCnt.PrimPerp.main | exact GlobalTheory.DegCnt.PrimPerp.main | (intros; apply GlobalTheory.DegCnt.PrimPerp.main <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePair_scalar_eq_quot_ideals_norm_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ N.Del ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ N.Del ∧ ∀ t : K, t * N.c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := by
  first | exact @GlobalTheory.DegCnt.c_eq_quot_ideals | exact GlobalTheory.DegCnt.c_eq_quot_ideals | (intros; apply GlobalTheory.DegCnt.c_eq_quot_ideals <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.card_innerLattices_with_definite_trace_le_norm : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ((({L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (N.NT ^ 2) := by
  first | exact @GlobalTheory.DegCnt.GlueZ.main | exact GlobalTheory.DegCnt.GlueZ.main | (intros; apply GlobalTheory.DegCnt.GlueZ.main <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular : ∀ (k r : ℕ) (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ → Rset k r g₀ = Set.range (fun x : UTin β → ℂ => uEmb k r (upperIn β x)) ∧ IsClosedSub k r (Rset k r g₀) ∧ IsHaarOn (Rset k r g₀) (lebR k r β) ∧ IsUnimod (Rset k r g₀) (lebR k r β) ∧ IsNormal k r β g₀⁻¹ ∧ (lebR k r β).map (conjM g₀) = lebR k r β := by
  first | exact @GlobalTheory.Amp.StabNormal.stabiliser_normal | exact GlobalTheory.Amp.StabNormal.stabiliser_normal | (intros; apply GlobalTheory.Amp.StabNormal.stabiliser_normal <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.stabilizer_measure_normalisation_symm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → γ ∈ GG k r ∧ IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ IsNormalFormStabilizerMeasure k r hj z' z γ⁻¹ s (μR.map (conjM γ)) ∧ 0 < Dj k r hj z z' γ ∧ Dj k r hj z' z γ⁻¹ = Dj k r hj z z' γ ∧ ∀ De, DeOK k r z z' γ De → DeOK k r z' z γ⁻¹ De := by
  first | exact @GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation | exact GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation | (intros; apply GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.lineLatticeClassMean_sum_nonzero_unfold : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 2 ≤ j → ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → latMean E j (fun L => w (covAt E j L) * ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ x.1) = glVol E (j - 1) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * j - 1)) * zetaE E j) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  exact @GlobalTheory.FlagBase.SiegelUnfold.latMean_sum_ne_zero
end

section

open NumberField MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.Amp.StabHaar

theorem normalFormStabilizerMeasure_eq_any_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (n₁ n₂ g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ) (μR : Measure (Mt k r)), n₁ ∈ Nset k r → n₂ ∈ Nset k r → IsNormal0 k r hj β c z z' g₀ → IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 μR → μR = (lebR0 k r j β).map (conjM n₂⁻¹) ∧ SigmaFinite (lebR0 k r j β) := by
  intro k r j hj z z' n₁ n₂ g₀ β c μR hn₁ hn₂ hg₀ hR
  obtain ⟨hz, hz', hT, -⟩ := id hR

  have hN : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 ((lebR0 k r j β).map (conjM n₂⁻¹)) := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by rw [ENNReal.ofReal_one, one_smul]⟩
  obtain ⟨-, hcl, hHaar, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 _ one_pos hN
  obtain ⟨-, -, hHaarR, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 μR one_pos hR

  obtain ⟨huniq, -, -⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos (2 * r + k + 1)
    (Rset k r (n₁ * g₀ * n₂)) ((lebR0 k r j β).map (conjM n₂⁻¹)) (matGroup hcl) hHaar
  obtain ⟨t, -, htop, ht⟩ := huniq μR hHaarR

  have hNt : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) t.toReal μR := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by
      rw [ht, ENNReal.ofReal_toReal htop.ne, Measure.map_smul]
      exact (conj_cont n₂⁻¹).measurable.aemeasurable⟩
  have h1 := normalFormStabilizerMeasure_scalar_le hj z z' _ 1 t.toReal μR hR hNt
  have h2 := normalFormStabilizerMeasure_scalar_le hj z z' _ t.toReal 1 μR hNt hR
  rw [ENNReal.ofReal_one, ENNReal.ofReal_toReal htop.ne] at h1 h2
  have ht1 : t = 1 := le_antisymm h2 h1
  obtain ⟨hH, -⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r j hj z z' g₀ β c hz hz' hT hg₀
  obtain ⟨hσ, -⟩ := hH
  exact ⟨by rw [ht, ht1, one_smul], hσ⟩

end GlobalTheory.Amp.StabHaar
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeSeenInDefiniteSpace_det_rank_index : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (H : Submodule D.host.E (hS D).V), WHyp D F (Wsp D) → H ≤ orth (hS D) (Xplus F) → H ⊓ Xsp F = ⊥ → ∀ N N' : LatV D, N ≤ toO (hS D) H → N' ≤ toO (hS D) H → detW D (seen D F N) = latDet (hS D) N ∧ rkW D (seen D F N) = finrank D.host.E (spanE (hS D) N) ∧ idxW D (seen D F N) (seen D F N') = idx (hS D) N N' := by
  first | exact @GlobalTheory.LoopC.SeenIso.main | exact GlobalTheory.LoopC.SeenIso.main | (intros; apply GlobalTheory.LoopC.SeenIso.main <;> assumption)
end
