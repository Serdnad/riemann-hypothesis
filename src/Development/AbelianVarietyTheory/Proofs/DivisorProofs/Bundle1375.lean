module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle115
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle166
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle161
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle188
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ),
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n → Formalism.IndefR.DatumF.ResEtaF χ n := by
  first | exact @GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow | exact GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow | (intros; apply GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Bridge Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.HeckeModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Group

variable {G : Type} [Group G]

theorem sum_eq_of_isDC {J : Subgroup G} {x x' : G} {A A' : Finset G} {F : G → ℂ} (hA : IsDC J x A) (hA' : IsDC J x' A')
    (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) (hF : ∀ k ∈ J, ∀ h, F (h * k) = F h) (h : G) :
    ∑ a ∈ A, F (h * a) = ∑ a ∈ A', F (h * a) :=
  congrFun (GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x' A A' F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA' hx
    (fun k h => by simpa using hF k k.2 h)).1 h

theorem sum_inv_of_isDC {J : Subgroup G} {x : G} {A : Finset G} {F : G → ℂ} (hA : IsDC J x A)
    (hF : ∀ k ∈ J, ∀ h, F (h * k) = F h) (k : G) (hk : k ∈ J) (h : G) :
    ∑ a ∈ A, F (h * k * a) = ∑ a ∈ A, F (h * a) := by
  have := (GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x A A F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA ⟨1, 1, by simp⟩
    (fun k h => by simpa using hF k k.2 h)).2 ⟨k, hk⟩ h
  simpa [dcOp] using this

theorem mem_of_isDC {K L : Subgroup G} (hKL : K ≤ L) {x : G} (hx : x ∈ L) {A : Finset G} (hA : IsDC K x A) :
    ∀ a ∈ A, a ∈ L := by
  intro a ha
  obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
  exact L.mul_mem (L.mul_mem (hKL k₁.2) hx) (hKL k₂.2)

structure Splits (J K L : Subgroup G) : Prop where
  le : K ≤ L
  mem : ∀ g ∈ L, g ∈ J ↔ g ∈ K
  dec : ∀ k ∈ J, ∃ k₁ ∈ K, ∃ k₂ ∈ J, k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l

theorem Splits.le' {J K L : Subgroup G} (hs : Splits J K L) : K ≤ J := fun g hg => (hs.mem g (hs.le hg)).2 hg

theorem Splits.isDC {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G} (hA : IsDC K x A) :
    IsDC J x A := by
  have hAL := mem_of_isDC hs.le hx hA
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
    exact ⟨⟨k₁, hs.le' k₁.2⟩, ⟨k₂, hs.le' k₂.2⟩, rfl⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a₁, ha₁, b₁, hb₁, e₁, c₁⟩ := hs.dec k₁ k₁.2
    obtain ⟨a, ⟨ha, hak⟩, -⟩ := hA.2 (a₁ * x) ⟨⟨a₁, ha₁⟩, 1, by simp⟩
    have hmem : a⁻¹ * (k₁ * x * k₂) ∈ J := by
      have : a⁻¹ * ((k₁ : G) * x * k₂) = a⁻¹ * (a₁ * x) * (b₁ * k₂) := by
        rw [e₁, mul_assoc a₁ b₁ x, (c₁ x hx).eq]; group
      rw [this]
      exact J.mul_mem (hs.le' hak) (J.mul_mem hb₁ k₂.2)
    refine ⟨a, ⟨ha, hmem⟩, ?_⟩
    rintro a' ⟨ha', hmem'⟩
    have h1 : a⁻¹ * a' ∈ J := by
      have : a⁻¹ * a' = (a⁻¹ * ((k₁ : G) * x * k₂)) * (a'⁻¹ * (k₁ * x * k₂))⁻¹ := by group
      rw [this]; exact J.mul_mem hmem (J.inv_mem hmem')
    have h2 : a⁻¹ * a' ∈ K := (hs.mem _ (L.mul_mem (L.inv_mem (hAL a ha)) (hAL a' ha'))).1 h1
    exact (hA.2 a' (hA.1 a' ha')).unique ⟨ha', by simp [K.one_mem]⟩ ⟨ha, h2⟩

theorem Splits.sum_transl {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G}
    (hA : IsDC K x A) {F : G → ℂ} (hF : ∀ k ∈ K, ∀ h, F (h * k) = F h) {κ : G} (hκ : κ ∈ J) (h : G) :
    ∑ a ∈ A, F (h * κ * a) = ∑ a ∈ A, F (h * a * κ) := by
  have hAL := mem_of_isDC hs.le hx hA
  obtain ⟨a₁, ha₁, b₁, -, rfl, c₁⟩ := hs.dec κ hκ
  have e1 : a₁ * b₁ = b₁ * a₁ := (c₁ a₁ (hs.le ha₁)).eq.symm
  rw [e1, ← mul_assoc, sum_inv_of_isDC hA hF a₁ ha₁]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← mul_assoc, hF a₁ ha₁, mul_assoc, (c₁ a (hAL a ha)).eq, mul_assoc]

end Group

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

structure OffAt (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (K large₂ : Subgroup (GA D V)) : Prop where
  splits : Splits (levG V β L) K large₂
  chi : ∀ k ∈ K, levChi V β L k = 1

theorem inv_of_mem_mult {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)} (hL : OffAt β L K large₂) {T : MMap M}
    (hT : T ∈ Mult θ M (levS V β L) (levChi V β L)) (v : M.Vec) : ∀ k ∈ K, ∀ h, T v (h * k) = T v h := by
  intro k hk h
  rw [((GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT).lev v k (hL.splits.le' hk) h, hL.chi k hk, one_mul]

theorem heckeOn_mem_mult {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)} (hL : OffAt β L K large₂) (hf : large₂ ≤ GfC V)
    {x : GA D V} (hx : x ∈ large₂) {A : Finset (GA D V)} (hA : IsDC K x A) {T : MMap M}
    (hT : T ∈ Mult θ M (levS V β L) (levChi V β L)) : heckeOn M A T ∈ Mult θ M (levS V β L) (levChi V β L) := by
  classical
  have hAL := mem_of_isDC hL.splits.le hx hA
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT
  have h0 : IsMultMap θ M ∅ (levChi V β L) T := ⟨hT'.aut, hT'.cusp, fun _ _ hk => absurd hk (Set.notMem_empty _), hT'.equiv, hT'.cont⟩
  have hex : ∀ a : GA D V, ∃ T' : MMap M, a ∈ A → IsMultMap θ M ∅ (levChi V β L) T' ∧ ∀ v, T' v = rTr V a (T v) := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨T', h⟩ := GlobalTheory.T.isMultMap_rightTranslate_finiteAdelic_normalizer θ M ∅ (levChi V β L) a (hf (hAL a ha))
        (fun k hk => absurd hk (Set.notMem_empty _)) T h0
      exact ⟨T', fun _ => h⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose Ta hTa using hex
  have e : heckeOn M A T = ∑ a ∈ A, Ta a := by
    ext v g
    rw [MultilinearMap.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a ha => (congrFun ((hTa a ha).2 v) g).symm
  have h1 : IsMultMap θ M ∅ (levChi V β L) (heckeOn M A T) := by
    rw [← GlobalTheory.MultMem.mem_mult_iff, e]
    exact Submodule.sum_mem _ fun a ha => Submodule.subset_span (hTa a ha).1
  refine Submodule.subset_span ⟨h1.aut, h1.cusp, fun v k hk g => ?_, h1.equiv, h1.cont⟩
  show ∑ a ∈ A, T v (g * k * a) = levChi V β L k * ∑ a ∈ A, T v (g * a)
  rw [hL.splits.sum_transl hx hA (inv_of_mem_mult hL hT v) hk, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => hT'.lev v k hk _

theorem heckeLin_actL {β : GL (Fin V.rank) (Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)}
    (hL : OffAt β (flagL L) K large₂) {x : GA D V} (hx : x ∈ large₂) {A : Finset (GA D V)} (hA : IsDC K x A)
    {F : GA D V → ℂ} (hF : ∀ k ∈ K, ∀ h, F (h * k) = F h) (g0 : Formalism.L2.DIV.G0 L.Pg L.r) :
    actL V β L g0 (heckeLin V A F) = heckeLin V A (actL V β L g0 F) := by
  funext h
  show actG0 V β L g0 (heckeLin V A F) h = ∑ a ∈ A, actG0 V β L g0 F (h * a)
  unfold actG0
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  · simp only [dif_pos hk]
    have hκ : hk.choose ∈ levG V β (flagL L) := ⟨hk.choose_spec.1, hk.choose_spec.2.1, Subgroup.mem_top _⟩
    rw [heckeLin_apply, hL.splits.sum_transl hx hA hF hκ, Finset.mul_sum]
  · simp [dif_neg hk]

theorem offAt_of_place {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hβ : IsBaseFrame V β Λ N) {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}
    (hL : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P) {K large₂ : Subgroup (GA D V)}
    (hLg : ∀ g, g ∈ large₂ ↔ SuppAt e V g) (hK : ∀ g, g ∈ K ↔ g ∈ locPart V (KsphC V ∅) e) : OffAt β L K large₂ := by
  have hp : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ N L hβ).2 P e _ hp hN hL
  obtain ⟨hf, hcf, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ hp
  have hc := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ hf hcf).2.2
  refine ⟨⟨fun g hg => (hLg g).2 ((hK g).1 hg).2, fun g hg => ?_, fun k hk => ?_⟩, fun k hk => ?_⟩
  · rw [h1 g ((hLg g).1 hg), hK]
    exact ⟨fun h => ⟨h, (hLg g).1 hg⟩, fun h => h.1⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, s₁, s₂, rfl⟩ := h3 k hk
    refine ⟨k₁, (hK _).2 ⟨(h1 _ s₁).1 hk₁, s₁⟩, k₂, hk₂, rfl, fun l hl => ?_⟩
    exact (hc (1 - (e + cA D e)) l k₂ (by rw [mul_sub, mul_one, hf, sub_self]) ((hLg l).1 hl) s₂).symm
  · have := (hK k).1 hk
    exact h2 k ((h1 k this.2).2 this.1) this.2

end GlobalTheory.HeckeModel
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

def conjMap (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) : MMap M' where
  toFun v' := star (T fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩)
  map_update_add' v' i x y := by
    have e : ∀ z : M'.sm i, (fun τ => (⟨c τ (Function.update v' i z τ), (h τ _).1 (Function.update v' i z τ).2⟩ : M.sm τ)) =
        Function.update (fun τ => (⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩ : M.sm τ)) i ⟨c i z, (h i _).1 z.2⟩ := by
      intro z
      funext τ
      by_cases hτ : τ = i
      · subst hτ; simp
      · simp [Function.update_of_ne hτ]
    rw [e, e, e, ← star_add, ← T.map_update_add]
    congr 3
    ext; simp
  map_update_smul' v' i a x := by
    have e : ∀ z : M'.sm i, (fun τ => (⟨c τ (Function.update v' i z τ), (h τ _).1 (Function.update v' i z τ).2⟩ : M.sm τ)) =
        Function.update (fun τ => (⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩ : M.sm τ)) i ⟨c i z, (h i _).1 z.2⟩ := by
      intro z
      funext τ
      by_cases hτ : τ = i
      · subst hτ; simp
      · simp [Function.update_of_ne hτ]
    rw [e, e]
    have e2 : (⟨c i ((a • x : M'.sm i) : M'.H i), (h i _).1 (a • x).2⟩ : M.sm i) = star a • ⟨c i x, (h i _).1 x.2⟩ := by
      ext; exact (c i).map_smulₛₗ a x
    rw [e2, T.map_update_smul, star_smul]
    simp only [RingHom.id_apply, star_star]

theorem conjMap_apply (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) (v' : M'.Vec) :
    conjMap M M' c h T v' = star (T fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) := rfl

theorem conjMap_eq_zero (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) (hT : conjMap M M' c h T = 0) : T = 0 := by
  refine MultilinearMap.ext fun v => ?_
  have h1 := congrArg (fun U : MMap M' => U fun τ => ⟨(c τ).symm (v τ), (h τ _).2 (by simpa using (v τ).2)⟩) hT
  simp only [conjMap_apply, LinearIsometryEquiv.apply_symm_apply, Subtype.coe_eta, MultilinearMap.zero_apply,
    star_eq_zero] at h1
  exact h1

theorem mult_congr (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {J : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (hχ : ∀ k ∈ J, χ' k = χ k) {T : MMap M} (hT : T ∈ Mult θ M J χ) : T ∈ Mult θ M J χ' := by
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  exact ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k hk g, hT.equiv, hT.cont⟩

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (J0 : Subgroup (GA D V)) {Pl0 : Type}
    (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg Sg' : Pl0 → ℂ[X])
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ))
    (hS : ∀ P k, (Sg' P).coeff k = star ((Sg P).coeff k)) :
    Module.rank ℂ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) ≤
      Module.rank ℂ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) := by
  obtain ⟨h, hM⟩ := GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc
  have key : ∀ T ∈ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)),
      conjMap M M' c h T ∈ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨T', hT', e1⟩ := hM J χ T h1
      have : conjMap M M' c h T = T' := by
        refine MultilinearMap.ext fun v' => funext fun g => ?_
        rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
        rfl
      rw [this]
      exact mult_congr θ M' hχ hT'
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
    · simp only [hPart, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at h3 ⊢
      intro P hP k hk α hα R hR
      have h4 := sub_eq_zero.1 (h3 P hP k hk α hα R hR)
      refine sub_eq_zero.2 (MultilinearMap.ext fun v' => funext fun g => ?_)
      have h5 : ∑ γ ∈ R, T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (g * γ) =
          ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g :=
        congrArg (fun U : MMap M => U (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g) h4
      show ∑ γ ∈ R, star (T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (g * γ)) =
          ((Sg' P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * star (T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g)
      rw [← star_sum, h5, hS]
      simp
  let j : (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) →+
      (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (J0 : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), (∀ k ∈ J, χ' k = star (χ k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) = Module.rank ℂ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q (fun P => (Sg P).map (starRingEnd ℂ)) : Submodule ℂ (MMap M')) := by
  intro D V S S' θ M M' c hc J χ χ' e e' J0 Pl0 ok pl q Sg hχ he
  refine le_antisymm (rank_le θ M M' c hc J χ χ' e e' J0 ok pl q Sg _ hχ he fun P k => by simp) ?_
  refine rank_le θ M' M (fun τ => (c τ).symm) ?_ J χ' χ e' e J0 ok pl q _ Sg ?_ ?_ ?_
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]
  · intro P k
    simp

end GlobalTheory.ConjDim

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hk3Core_and_tup_mu_of_weakCharacterisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.Hk3.Core R.toRealDat F.lv2 ∧ R.toRealDat.tup_mu_off ∧ R.toRealDat.tup_mu_used := by
  first | exact @GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face | exact GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face | (intros; apply GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare.TameConj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions (idealHat CongMod)
open GlobalTheory.IdemSupport (mem_intAE_iff parts_cA finPart_cA_mem)

variable {D : D7}

theorem mul_mem_intAE {y z : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) (hz : z ∈ intAE D) :
    y * z ∈ intAE D := by
  rw [mem_intAE_iff] at hy hz ⊢
  rw [RingHom.map_mul]
  exact mul_mem hy hz

theorem FinUnit_mul {x y : (AE D)ˣ} (hx : FinUnit x) (hy : FinUnit y) : FinUnit (x * y) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, RingHom.map_mul, hx.1, hy.1, one_mul]
  · rw [Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.1 hy.2.1
  · rw [mul_inv, Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.2 hy.2.2

theorem FinUnit_inv {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit x⁻¹ := by
  refine ⟨?_, hx.2.2, hx.2.1⟩
  have e : infPart D (x : AE D) * infPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  rwa [hx.1, one_mul] at e

theorem FinUnit_conj {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit (Units.map (cA D).toMonoidHom x) := by
  refine ⟨?_, finPart_cA_mem hx.2.1, finPart_cA_mem hx.2.2⟩
  exact (parts_cA (x : AE D)).1.trans (by rw [hx.1, RingHom.map_one])


end GlobalTheory.GeoActCompare.TameConj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LatticeIndex

theorem intersected_trivAt_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (ℓ : ℕ), ℓ.Prime → Λ.TrivAt ℓ → ∀ la : HeightOneSpectrum (𝓞 c.F), (ℓ : 𝓞 c.F) ∈ la.asIdeal → ∀ s : c.F, Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → la.valuation c.F s ≤ 1 := by
  intro E _ _ _ H Dw l c n Λ ℓ hℓ hT la hla s hs
  obtain ⟨k, hk, hkLa, hkstd⟩ := hT
  set w := la.valuation c.F with hwdef
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => la.valuation_le_one r
  have hwi : ∀ x : c.F, IsIntegral ℤ x → w x ≤ 1 := fun x hx => hw ⟨x, hx⟩
  have hk1 : w (k : c.F) = 1 := by
    have h := (la.valuation_eq_one_iff_notMem (K := c.F) (r := (k : 𝓞 c.F))).2 ?_
    · simpa using h
    · intro hm
      obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 c.F) hk)
      have : (1 : 𝓞 c.F) ∈ la.asIdeal := by
        rw [← hab]
        exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hm) (la.asIdeal.mul_mem_left _ hla)
      exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hkv : ∀ τ : E →+* ℂ, w (embF c τ (k : E)) = 1 := fun τ => by rw [map_natCast]; exact hk1
  have hsm : ∀ v : Fin n → Fin n → E,
      (Matrix.of fun i j => ((k : 𝓞 E) • v j) i) = (k : E) • Matrix.of fun i j => v j i := by
    intro v; ext i j; simp [Algebra.smul_def]
  have hdetk : ∀ v : Fin n → Fin n → E,
      Matrix.det (Matrix.of fun i j => ((k : 𝓞 E) • v j) i) = (k : E) ^ n * Matrix.det (Matrix.of fun i j => v j i) := by
    intro v; rw [hsm, Matrix.det_smul, Fintype.card_fin]

  have hei : ∀ i : Fin n, (k : 𝓞 E) • (Pi.single i 1 : Fin n → E) ∈ Λ.Ln := fun i =>
    ⟨hkstd (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (single_std i)),
      Submodule.smul_mem _ _ (single_std i)⟩
  have hdete : Matrix.det (Matrix.of fun i j => ((k : 𝓞 E) • (Pi.single j 1 : Fin n → E)) i) = (k : E) ^ n := by
    rw [hdetk, det_single, _root_.mul_one]
  have hLa : ∀ τ : E →+* ℂ, HasMax w (idealAt c Λ.La τ) 1 := fun τ => by
    refine hasMax_span hw ?_ ⟨_, ⟨_, ⟨_, fun i => (hei i).1, rfl⟩, rfl⟩, ?_⟩
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      have hu : ∀ i, (k : 𝓞 E) • v i ∈ stdLat E n := fun i =>
        hkLa (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hv i))
      obtain ⟨r, hr⟩ := det_std hu
      rw [hdetk] at hr
      have h := hwi _ (map_isIntegral_int (embF c τ) r.isIntegral_coe)
      rw [hr] at h
      simp only [map_mul, map_pow, hkv, one_pow, _root_.one_mul] at h
      exact h
    · rw [hdete]; simp only [map_pow, hkv, one_pow]
  have hLn : ∀ τ : E →+* ℂ, HasMax w (idealAt c Λ.Ln τ) 1 := fun τ => by
    refine hasMax_span hw ?_ ⟨_, ⟨_, ⟨_, hei, rfl⟩, rfl⟩, ?_⟩
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact (hLa τ).1 _ (Submodule.subset_span ⟨_, ⟨v, fun i => (hv i).1, rfl⟩, rfl⟩)
    · rw [hdete]; simp only [map_pow, hkv, one_pow]
  have hb : HasMax w (Submodule.span (𝓞 c.F) {s}) (w s) := hasMax_span hw (by simp) (by simp)
  have e1 := hb.mul (hasMax_prod hw Finset.univ _ _ fun τ => (hLn τ).pow hw (Dw.mult τ))
  have e2 := hasMax_prod hw Finset.univ _ _ fun τ => (hLa τ).pow hw (Dw.mult τ)
  obtain ⟨y, hy, hyw⟩ := e1.2
  have := e2.1 y (hs hy)
  simpa [hyw] using this

end GlobalTheory.LatticeIndex
end
end
