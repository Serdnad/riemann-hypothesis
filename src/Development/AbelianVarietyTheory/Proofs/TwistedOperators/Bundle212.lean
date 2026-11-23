module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle200
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle456
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle316
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle201
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.InertDbl.inlD_mem_KAtD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)),
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈ GlobalTheory.InertDbl.KAtD σ W v := by
  apply GlobalTheory.InertBigCell.inlD_mem <;> assumption
end

section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CompactLine

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, inclR, compInf, infEmb_tmul]

theorem commute_of_gen {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (C : Matrix β (Ix R S) ℂ)
    (A' : Matrix (Ix R S) β ℂ) (hCA : C * A' = 1) (g θ : Matrix β β ℂ) (Y : Mat R S) (hY : IsKC Y) (t : ℝ)
    (hθ : θ * C = C * Jm R S) (hg : g * C = C * NormedSpace.exp (t • Y)) : Commute g θ := by
  have h1 : Commute Y (Jm R S) := (GlobalTheory.CartanInt.UnitLog.isKC_iff_commute Y).1 hY
  have h2 : Commute (NormedSpace.exp (t • Y)) (Jm R S) := (h1.smul_left t).exp_left
  have h3 : g * θ * C = θ * g * C := by
    rw [Matrix.mul_assoc, hθ, ← Matrix.mul_assoc, hg, Matrix.mul_assoc θ, hg, ← Matrix.mul_assoc θ, hθ,
      Matrix.mul_assoc, Matrix.mul_assoc, h2.eq]
  calc g * θ = g * θ * C * A' := by rw [Matrix.mul_assoc _ C, hCA, Matrix.mul_one]
    _ = θ * g := by rw [h3, Matrix.mul_assoc _ C, hCA, Matrix.mul_one]

theorem exists_line_in_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, γ (Multiplicative.ofAdd (1 : ℝ)) = k ∧
      ∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb := by
  intro F E _ _ _ _ _ σ B n X r s hb hX k hk
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds n r s _ (X.θ w) (hX.sig w) (hX.cartan w)
  have hA1 : ∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  obtain ⟨γ, hγ, Y, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin n) r s
    B.emb (incM F X.J) 1 A X.θ hb.cm hA1 hAθ k hk.1 hk.2
  refine ⟨γ, hγ, hγ1, fun t => ⟨hγ.2 t, fun w => ?_⟩⟩
  obtain ⟨A', hAA⟩ := (hA w).2
  exact commute_of_gen (A w) A' hAA _ _ (Y w) (hKC w) t.toAdd (hAθ w) (hgen t.toAdd w)

end GlobalTheory.CompactLine

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical


theorem _root_.GlobalTheory.T.unitaryArchimedeanLine_pair_operators_oneParameter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        (∀ (s t : ℝ) (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  first | exact @GlobalTheory.LineGroupPair.archOp_oneParam_pair | exact GlobalTheory.LineGroupPair.archOp_oneParam_pair | (intros; apply GlobalTheory.LineGroupPair.archOp_oneParam_pair <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

theorem _root_.GlobalTheory.T.weil_representation_integral_action : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → ∀ (μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
    ∀ (h : UA σ W.J) (f f₁ : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, h)) ⇑f ⇑f₁ →
      ∫ x, ‖f₁ x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchIsom.acts_norm_sq_eq | exact GlobalTheory.ArchIsom.acts_norm_sq_eq | (intros; apply GlobalTheory.ArchIsom.acts_norm_sq_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.LFun.SatBoundGL

private theorem mem_adicCompletionIntegers_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) :
    letI := GlobalTheory.LocalData.complRel w
    x ∈ Valuation.integer (ValuativeRel.valuation (w.adicCompletion E)) ↔ x ∈ w.adicCompletionIntegers E := by
  letI := GlobalTheory.LocalData.complRel w
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [Valuation.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  simpa using h x 1


open ValuativeRel in
theorem resCard_completion {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    GlobalTheory.SplitWeil.resCard (w.adicCompletion E) = Ideal.absNorm w.asIdeal := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w

  let e : Valuation.integer (ValuativeRel.valuation (w.adicCompletion E)) ≃+* w.adicCompletionIntegers E :=
    { toFun := fun x => ⟨x.1, (mem_adicCompletionIntegers_iff w x.1).1 x.2⟩
      invFun := fun y => ⟨y.1, (mem_adicCompletionIntegers_iff w y.1).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  unfold GlobalTheory.SplitWeil.resCard
  rw [Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv, Formalism.UG.P.tjcosets_card_residue w]
  rfl

theorem norm_le_of_hasSatGL : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsIrrSmooth ρ → GlobalTheory.LGrp.IsUnitarisable ρ → HasSatGL w ρ B → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  intro hT E _ _ w n V _ _ ρ B hirr hun hsat b hb
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  obtain ⟨hsph, hvec⟩ := hsat

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hsph
  have hG : LGrp.HasSatakeGL ρ B := GlobalTheory.LFun.SatCompare.hasSatakeGL_of_isSatVecGL hirr (hvec x hx hx0)
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ ρ B).mp hG
  have hR := hT (w.adicCompletion E) n V ρ α hirr.1 hirr.2 ((GlobalTheory.LGrp.isUnitarisable_iff ρ).mp hun) ?_ hα
  · rw [← hαB] at hb
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hb
    have hi := (hR i).2
    rwa [resCard_completion] at hi
  · unfold GlobalTheory.SmGL.IsSpherical
    exact (GlobalTheory.LGrp.isSpherical_iff ρ _).mp hG.2

end GlobalTheory.LFun.SatBoundGL
end

section

open Formalism.UG (IsUnramInv GU KU Hecke dosetInd)

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists

open Formalism.UG

section Generic

variable {G : Type} [Group G] {K : Subgroup G}

def cosetsIn (K : Subgroup G) (g : G) : Set (G ⧸ K) := {x | ∃ a b : K, x.out = (a : G) * g * b}

theorem mem_cosetsIn_iff (x : G ⧸ K) (t : G) :
    x ∈ cosetsIn K t ↔ x.out ∈ DoubleCoset.doubleCoset t (K : Set G) K := by
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨fun ⟨a, b, e⟩ => ⟨a, a.2, b, b.2, e⟩, fun ⟨a, ha, b, hb, e⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩⟩

theorem cosetsIn_eq {g g' : G} (h : g' ∈ DoubleCoset.doubleCoset g (K : Set G) K) :
    cosetsIn K g' = cosetsIn K g := by
  ext x
  rw [mem_cosetsIn_iff, mem_cosetsIn_iff, DoubleCoset.doubleCoset_eq_of_mem h]

theorem dosetInd_eq {g g' : G} (h : g' ∈ DoubleCoset.doubleCoset g (K : Set G) K) :
    dosetInd ℂ K g' = dosetInd ℂ K g := by
  rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem h]

theorem cosetsIn_ncard_ne_zero (hK : IsCommensurated K) (g : G) : (cosetsIn K g).ncard ≠ 0 := by
  refine ((Set.ncard_pos (P.finite_cosets_in_doset hK g)).2 ⟨(g : G ⧸ K), ?_⟩).ne'
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K g
  exact ⟨1, u, by simpa using hu⟩

theorem cosetsIn_one : cosetsIn K 1 = {((1 : G) : G ⧸ K)} := by
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, e⟩
    rw [← QuotientGroup.out_eq' x, e]
    exact QuotientGroup.eq.2 (by simpa using K.inv_mem (K.mul_mem a.2 b.2))
  · rintro rfl
    refine ⟨⟨((1 : G) : G ⧸ K).out, ?_⟩, 1, by simp⟩
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : G) : G ⧸ K))
    simpa using K.inv_mem this

end Generic

theorem exists_isZonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α : Fin (n / 2) → ℂˣ, ∃ w : GU σ n → ℂ,
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal ϖ q α w := by
  intro L _ _ _ ϖ σ q n hU α
  classical
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have law := GlobalTheory.LFun.SatCompare.satU_laws (n := n) hU α
  have hN : ∀ g : GU σ n, ((cosetsIn (KU σ n) g).ncard : ℂ) ≠ 0 := fun g =>
    Nat.cast_ne_zero.2 (cosetsIn_ncard_ne_zero hK g)
  let w : GU σ n → ℂ := fun g =>
    SatU ϖ q (dosetInd ℂ (KU σ n) g) (fun i => (α i : ℂ)) / ((cosetsIn (KU σ n) g).ncard : ℂ)
  have hw : ∀ g g' : GU σ n, g' ∈ DoubleCoset.doubleCoset g (KU σ n : Set (GU σ n)) (KU σ n) → w g' = w g :=
    fun g g' h => by simp only [w, dosetInd_eq h, cosetsIn_eq h]
  refine ⟨w, fun a b g => hw _ _ (DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, b, b.2, rfl⟩), ?_, fun h hh => ?_⟩
  · simp only [w, law.2.2, cosetsIn_one, Set.ncard_singleton, Nat.cast_one, div_one]
  refine GlobalTheory.LFun.hecke_induction (K := KU σ n)
    (p := fun f => hAct (KU σ n) f w 1 = SatU ϖ q f fun i => (α i : ℂ)) ?_ ?_ ?_ hh
  · simpa [hAct] using (law.2.1 0 0 (zero_mem _)).symm
  · intro f hf f' hf' e e'
    have fin : ∀ f ∈ Hecke ℂ (KU σ n), (Function.support fun x : GU σ n ⧸ KU σ n => f x.out • w (1 * x.out)).Finite :=
      fun f hf => (P.finite_support_cosets hK hf.2).subset fun x hx h0 => hx (by simp [h0])
    rw [law.1 _ hf _ hf', ← e, ← e', hAct, hAct, hAct]
    simp only [Pi.add_apply, add_smul]
    exact finsum_add_distrib (fin f hf) (fin f' hf')
  · intro r g
    have hfin := P.finite_cosets_in_doset hK g
    have hterm : ∀ x ∈ hfin.toFinset, (r • dosetInd ℂ (KU σ n) g) x.out • w (1 * x.out) = r * w g := fun x hx => by
      have hm := (mem_cosetsIn_iff x g).1 ((Set.Finite.mem_toFinset _).1 hx)
      rw [Pi.smul_apply, dosetInd, Set.indicator_of_mem hm, one_mul, hw g _ hm]
      simp
    rw [law.2.1 r _ (Final.DosetIndMem _ _ ℂ g), hAct,
      finsum_eq_sum_of_support_subset (s := hfin.toFinset), Finset.sum_congr rfl hterm,
      Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul]
    · have := hN g
      simp only [w]
      rw [← cosetsIn]
      field_simp
    · intro x hx
      rw [Set.Finite.coe_toFinset]
      by_contra h
      refine hx ?_
      show (r • dosetInd ℂ (KU σ n) g) x.out • w (1 * x.out) = 0
      rw [Pi.smul_apply, dosetInd, Set.indicator_of_notMem (fun h' => h ((mem_cosetsIn_iff x g).2 h'))]
      simp

end GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists
end
end

section

namespace GlobalTheory.CoverModel

theorem modelsAreCoverSeries_all :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  modelsAreCoverSeries

end GlobalTheory.CoverModel
end

section

open scoped Matrix

namespace GlobalTheory.StdChainStab

open Matrix

variable {K : Type} [Field K] {n m : ℕ}

def lowVec (b : Fin n → Fin m) (j : ℕ) (w : Fin n → K) : Prop :=
  ∀ i : Fin n, j ≤ ((b i : Fin m) : ℕ) → w i = 0

theorem lowVec_single (b : Fin n → Fin m) (c : Fin n) :
    lowVec b ((b c : ℕ) + 1) (Pi.single c (1 : K)) := by
  intro i hi
  have : i ≠ c := by rintro rfl; omega
  simp [Pi.single_apply, this]

theorem mulVec_single_apply (z : Matrix (Fin n) (Fin n) K) (i c : Fin n) :
    (z *ᵥ Pi.single c (1 : K)) i = z i c := by
  simp [Matrix.mulVec_single_one]

theorem stab_iff (b : Fin n → Fin m) (z : Matrix (Fin n) (Fin n) K) :
    (∀ j : Fin (m + 1), ∀ w, lowVec b j w → lowVec b j (z *ᵥ w)) ↔
      ∀ i c, b c < b i → z i c = 0 := by
  constructor
  · intro H i c hic
    have h1 := H ⟨(b c : ℕ) + 1, by omega⟩ _ (lowVec_single b c) i (by simp; exact hic)
    rwa [mulVec_single_apply] at h1
  · intro H j w hw i hi
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : (j : ℕ) ≤ (b c : ℕ)
    · rw [hw c hc, mul_zero]
    · rw [H i c (by rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]

theorem rad_iff (b : Fin n → Fin m) (z : Matrix (Fin n) (Fin n) K) :
    (∀ j : Fin m, ∀ w, lowVec b (j.succ : ℕ) w → lowVec b (j.castSucc : ℕ) (z *ᵥ w - w)) ↔
      ∀ i c, ¬ b i < b c → z i c = (1 : Matrix (Fin n) (Fin n) K) i c := by
  constructor
  · intro H i c hic
    have h1 := H (b c) _ (by simpa using lowVec_single (K := K) b c) i
      (by simp; exact (not_lt.1 hic))
    rw [Pi.sub_apply, mulVec_single_apply, sub_eq_zero] at h1
    simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using h1
  · intro H j w hw i hi
    have e : z *ᵥ w - w = (z - 1) *ᵥ w := by rw [sub_mulVec, one_mulVec]
    rw [e]
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : (j : ℕ) + 1 ≤ (b c : ℕ)
    · rw [hw c (by simpa using hc), mul_zero]
    · simp only [Fin.coe_castSucc] at hi
      rw [Matrix.sub_apply, H i c (by rw [Fin.lt_iff_val_lt_val]; omega), sub_self, zero_mul]

theorem transport (Gm Gi X : Matrix (Fin n) (Fin n) K) (h1 : Gi * Gm = 1) (h2 : Gm * Gi = 1)
    (P : (Fin n → K) → Prop) (Q : (Fin n → K) → (Fin n → K) → Prop) :
    (∀ y, P (Gi *ᵥ y) → Q (Gi *ᵥ y) (Gi *ᵥ (X *ᵥ y))) ↔ ∀ w, P w → Q w ((Gi * X * Gm) *ᵥ w) := by
  constructor
  · intro H w hw
    have hw' : Gi *ᵥ (Gm *ᵥ w) = w := by rw [mulVec_mulVec, h1, one_mulVec]
    have := H (Gm *ᵥ w) (by rw [hw']; exact hw)
    rw [hw'] at this
    simpa [mulVec_mulVec, Matrix.mul_assoc] using this
  · intro H y hy
    have := H _ hy
    simpa [mulVec_mulVec, Matrix.mul_assoc, h2] using this

theorem stdChain_stab_rad : ∀ {K : Type} [Field K] {n m : ℕ} (Y : Fin (m + 1) → Submodule K (Fin n → K)) (d : Fin m → ℕ) (h : ∑ j, d j = n)
    (g : GL (Fin n) K), (∀ (j : Fin (m + 1)) (y : Fin n → K),
      y ∈ Y j ↔ ∀ i : Fin n, (j : ℕ) ≤ ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) i : Fin m) : ℕ) →
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) i = 0) →
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.parab K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j, ∀ y ∈ Y j, (x : Matrix (Fin n) (Fin n) K) *ᵥ y ∈ Y j) ∧
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.unipRad K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j : Fin m, ∀ y ∈ Y j.succ, (x : Matrix (Fin n) (Fin n) K) *ᵥ y - y ∈ Y j.castSucc) := by
  intro K _ n m Y d h g hY
  set b := GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) with hb
  have hGi : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGm : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hz : ∀ x : GL (Fin n) K, (((g⁻¹ * x * g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) *
        (g : Matrix (Fin n) (Fin n) K) := fun x => by simp only [Units.val_mul]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.SmGL.mem_parab, hz, ← stab_iff]
    refine forall_congr' fun j => ?_
    have := transport (g : Matrix (Fin n) (Fin n) K) ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (x : Matrix (Fin n) (Fin n) K) hGi hGm (lowVec b j) (fun _ v => lowVec b j v)
    rw [← this]
    refine forall_congr' fun y => ?_
    rw [hY j y, hY j]
    rfl
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.RadRev.mem_unipRad_entries, hz, ← rad_iff]
    refine forall_congr' fun j => ?_
    have := transport (g : Matrix (Fin n) (Fin n) K) ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (x : Matrix (Fin n) (Fin n) K) hGi hGm (lowVec b (j.succ : ℕ)) (fun w v => lowVec b (j.castSucc : ℕ) (v - w))
    rw [← this]
    refine forall_congr' fun y => ?_
    rw [hY j.succ y, hY j.castSucc, mulVec_sub]
    rfl

end GlobalTheory.StdChainStab
end

section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

theorem _root_.GlobalTheory.T.integral_compactOpenTypeIdempotent_unipotent_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W)
    [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k))
    (N : Subgroup (GL (Fin r) k)) (ν : Measure N) [ν.IsMulLeftInvariant] (H : Subgroup (GL (Fin r) 𝓀[k])),
    NoFixed τ H → ∀ x : GL (Fin r) k,
    (∀ v ∈ H, ∃ n ∈ N, ∃ hn : x * n * x⁻¹ ∈ KO k (Fin r), GlobalTheory.LocGL.redK k (Fin r) ⟨x * n * x⁻¹, hn⟩ = v) →
    ∀ w : GL (Fin r) k, ∫ u : N, idemGL k μ τ (x * u * w) ∂ν = 0 := by
  first | exact @GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero | exact GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero | (intros; apply GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero <;> assumption)
end

section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

theorem _root_.GlobalTheory.T.mem_stdMaxParabolic_of_blockParabolic_le_conj : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ) (hd : ∑ i, d i = r) (g : GL (Fin r) F),
    parab F (stdBlocks d hd) ≤ conjBy g (stdMaxParab F h) → g ∈ stdMaxParab F h := by
  first | exact @GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | exact GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | (intros; apply GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy <;> assumption)
end

section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

theorem _root_.GlobalTheory.T.reduction_maxCompact_inter_conjRadical_contains_conj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r a b : ℕ}
    (h : a + b = r) (g₀ : GL (Fin r) k), ∃ c : GL (Fin r) 𝓀[k], ∀ v ∈ stdMaxRad 𝓀[k] h,
    ∃ (u : GL (Fin r) k) (hu : u ∈ KO k (Fin r)), u ∈ conjBy g₀ (stdMaxRad k h) ∧
      GlobalTheory.LocGL.redK k (Fin r) ⟨u, hu⟩ = c * v * c⁻¹ := by
  first | exact @GlobalTheory.RadRedLift.red_lift | exact GlobalTheory.RadRedLift.red_lift | (intros; apply GlobalTheory.RadRedLift.red_lift <;> assumption)
end

section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

theorem _root_.GlobalTheory.T.stdMaxParabolicRadical_le_blockUnipotentRadical : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ) (hd : ∑ i, d i = r),
    parab F (stdBlocks d hd) ≤ stdMaxParab F h → stdMaxRad F h ≤ unipRad F (stdBlocks d hd) := by
  first | exact @GlobalTheory.RadRev.stdMaxRad_le_unipRad | exact GlobalTheory.RadRev.stdMaxRad_le_unipRad | (intros; apply GlobalTheory.RadRev.stdMaxRad_le_unipRad <;> assumption)
end
