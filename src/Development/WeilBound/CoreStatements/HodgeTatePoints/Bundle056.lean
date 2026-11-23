module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle036
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle110
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonemptyRingHomComplex
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplex
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_datum_tate_complex (T : GlobalTheory.CM.PAT H (Sp ℂ)) (hg : 1 ≤ T.g) (p q : ℕ)
    (hty : ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ p) ∧
      (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ q)) :
    ∃ D : Datum H, D.p = p ∧ D.q = q ∧ 1 ≤ p + q ∧
      Nonempty (TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ T.t.G) (fun a g => g ≫ T.t.act.act a)
        (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))) := by
  have hT := GlobalTheory.thetaUnifAV_all
  obtain ⟨g, ty, hfn⟩ := GlobalTheory.AllClasses.exists_isTypeFn H p q
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, -, hW⟩ := hT T.pol T.t.PP.rig T.t.PP.rigGen
  obtain ⟨D, Pe, F, hp, hq, hP, hF, hEF, hact⟩ :=
    GlobalTheory.CM.PureTriple.exists_datum_period hT GlobalTheory.firstFiveLaws.1 T hfn hty u hAH
  refine ⟨D, hp, hq, ?_, ?_⟩
  · have hgg : g = T.g := by simpa using F.finrank_eq
    let j : Fin g := ⟨0, by omega⟩
    have : Nonempty {i // ty i = ty j} := ⟨⟨j, rfl⟩⟩
    have hc : 0 < Nat.card {i // ty i = ty j} := Nat.card_pos
    by_cases h : ty j (H.rt : E) = H.rt0
    · have := (hfn _).1 h
      omega
    · have := (hfn _).2 h
      omega
  · obtain ⟨I, -⟩ := GlobalTheory.UnifObj.exists_tateIso D D ty Pe (Q := 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G)
      (fun a g => g ≫ T.t.act.act a) (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))
      (fun z => u.ex (F z)) (fun _ => LinearMap.id) hP.1 hP.2.1 (fun z z' => by rw [map_add (f := _), u.ex_add])
      (u.ex_onto.comp F.surjective) (fun z => (u.ker _).trans (hF z)) hact
      (fun k a b c hk hc => by
        have ha : F (Pe a) ∈ u.Λ := (hF _).2 ⟨a, rfl⟩
        have hb : F (Pe b) ∈ u.Λ := (hF _).2 ⟨b, rfl⟩
        have e : Ef ⟨_, ha⟩ ⟨_, hb⟩ = D.EF a b := by
          have := (hE ⟨_, ha⟩ ⟨_, hb⟩).trans (hEF a b)
          exact_mod_cast this
        have := hW k ⟨_, ha⟩ ⟨_, hb⟩ c hk (by rw [e]; exact hc)
        simp only [map_smul]
        exact this)
      (fun n m _ _ a => ⟨0, by simp⟩) (fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩)
      (fun n _ a a' => by simp)
    exact ⟨I⟩

theorem exists_countable_algClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] (s : Set Ω) (hs : s.Countable) :
    ∃ K₀ : Subfield Ω, s ⊆ K₀ ∧ Countable K₀ ∧ IsAlgClosed K₀ := by
  let F := Subfield.closure s
  have hF : Countable F := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max s).trans (max_le ?_ le_rfl)
    exact Cardinal.mk_le_aleph0_iff.2 hs.to_subtype
  refine ⟨(algebraicClosure F Ω).toSubfield, fun x hx => ?_, ?_, ?_⟩
  · exact (algebraicClosure F Ω).algebraMap_mem (⟨x, Subfield.subset_closure hx⟩ : F)
  · show Countable (algebraicClosure F Ω)
    rw [← Cardinal.mk_le_aleph0_iff]
    set_option synthInstance.maxHeartbeats 200000 in
      exact (Algebra.IsAlgebraic.cardinalMk_le_max F _).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  · show IsAlgClosed (algebraicClosure F Ω)
    exact IsAlgClosure.isAlgClosed F

theorem exists_pat_descent {Ω : Type} [Field Ω] [IsAlgClosed Ω] (T : GlobalTheory.CM.PAT H (Sp Ω)) :
    ∃ (K₀ : Subfield Ω) (T₀ : GlobalTheory.CM.PAT H (Sp K₀)) (φ : T.t.G.left ⟶ T₀.t.G.left), Countable K₀ ∧ IsAlgClosed K₀ ∧
      T₀.g = T.g ∧ IsGrpPullback T.t.G T₀.t.G (spMap K₀.subtype) φ ∧ LBIso T.t.PP.L (T₀.t.PP.L.pull φ) ∧
      ∀ a, (T.t.act.act a).left ≫ φ = φ ≫ (T₀.t.act.act a).left := by
  have hL := GlobalTheory.firstFiveLaws.1
  obtain ⟨R₁, _, _, P₁, j, hc₁, hG, hiso, hgg⟩ := GlobalTheory.KeyCountableDescent.exists_polAV_descent hL Ω T.pol
  have := P₁.isAb.proper
  have := P₁.isAb.smooth
  choose S hS using fun a : 𝓞 E => GlobalTheory.morphism_descends_to_subring Ω R₁ T.t.G.left P₁.A.left P₁.A.left T.t.G.hom
    P₁.A.hom P₁.A.hom j ((T.t.act.act a).left ≫ j) hG.1 (by
      have w : j ≫ P₁.A.hom = T.t.G.hom ≫ spMap R₁.subtype := hG.1.w
      rw [Category.assoc, w, ← Category.assoc, Over.w])
  have hcE : Countable (𝓞 E) := (RingOfIntegers.basis E).repr.injective.countable
  obtain ⟨K₀, hsub, hcK, hK⟩ := exists_countable_algClosed ((R₁ : Set Ω) ∪ ⋃ a, (S a : Set Ω))
    ((Set.countable_coe_iff.1 hc₁).union (Set.countable_iUnion fun a => (S a).countable_toSet))
  have h₁ : R₁ ≤ K₀.toSubring := fun x hx => hsub (Or.inl hx)
  let f : R₁ →+* K₀ := Subring.inclusion h₁
  obtain ⟨P₂, π, hπ⟩ := GlobalTheory.exists_isPolFibre hL.polBaseChange f P₁
  obtain ⟨ψ, hψ, hψ'⟩ := GlobalTheory.CM.EllComp.exists_isPolFibre_lift (g := K₀.subtype) (P'' := T.pol) (χ := j) hπ
    ⟨hgg, hG, hiso.symm⟩
  have hψG : IsGrpPullback T.t.G P₂.A (spMap K₀.subtype) ψ := hψ'.2.1
  have hfl := GlobalTheory.FieldBaseChange.flat_spMap K₀.subtype
  have hsj := GlobalTheory.FieldBaseChange.surjective_spMap K₀.subtype
  obtain ⟨r, hr⟩ := GlobalTheory.ActDescent.exists_oAct hψG T.t.act fun a => by
    obtain ⟨b, b₁, b₂⟩ := hS a K₀.toSubring h₁ (fun x hx => hsub (Or.inr (Set.mem_iUnion.2 ⟨a, hx⟩))) P₂.A.left P₂.A.hom
      π ψ hπ.2.1.1 hψ hψG.1.w
    have w : b ≫ P₁.A.hom = P₂.A.hom ≫ spMap f := b₂.trans hπ.2.1.1.w
    refine ⟨Over.homMk (hπ.2.1.1.lift b _ w) (hπ.2.1.1.lift_snd _ _ _), hπ.2.1.1.hom_ext ?_ ?_⟩
    · show _ = (ψ ≫ hπ.2.1.1.lift b _ w) ≫ π
      rw [Category.assoc, hψ, Category.assoc, IsPullback.lift_fst, b₁]
    · show _ = (ψ ≫ hπ.2.1.1.lift b _ w) ≫ _
      rw [Category.assoc, Category.assoc, IsPullback.lift_snd, hψG.1.w, ← Category.assoc, Over.w]
  obtain ⟨τ₀, e, he, heL, heact⟩ := GlobalTheory.exists_triple_of_fieldExtension hL E H K₀ Ω K₀.subtype T.t P₂.A ψ P₂.L r P₂.isAb
    hψG P₂.isLB hψ'.2.2.symm hr
  have hE := isGrpPullback_of_iso e
  obtain ⟨h₁', h₂, h₃⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally _ _ P₂.A τ₀.G _ _
    P₂.L τ₀.PP.L P₂.isLB τ₀.PP.isLB P₂.isAb hE heL
  have hs : Out.Sym τ₀.G τ₀.PP.L := by
    obtain ⟨-, w, hw, -⟩ := τ₀.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  have hd : SmoothOfRelativeDimension P₂.g τ₀.G.hom :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} P₂.g
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension P₂.g) hE.1 P₂.smoothDim
  have hinv : (ψ ≫ e.inv.left) ≫ e.hom.left = ψ := by
    rw [Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.comp_id]
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  refine ⟨K₀, ⟨τ₀, h₁', P₂.g, hd, hs, h₂ P₂.ample, h₃ P₂.ktriv⟩, ψ ≫ e.inv.left, hcK, hK, hψ'.1.symm,
    (hψG.comp (isGrpPullback_of_iso e.symm)).congr (Category.comp_id _) rfl, ?_, fun a => ?_⟩
  · refine LBIso.trans T.t.PP.isLB (pull_isLB P₂.isLB ψ) (pull_isLB τ₀.PP.isLB _) hψ'.2.2.symm ?_
    have := GlobalTheory.CM.EllComp.lbIso_pull_comp heL.symm (ψ ≫ e.inv.left)
    rwa [hinv] at this
  · have e₁ : r.act a ≫ e.inv = e.inv ≫ τ₀.act.act a := by
      rw [Iso.comp_inv_eq, Category.assoc, heact, Iso.inv_hom_id_assoc]
    show _ = (ψ ≫ e.inv.left) ≫ (τ₀.act.act a).left
    rw [← Category.assoc, hr, Category.assoc, Category.assoc, ← Over.comp_left, e₁, Over.comp_left]

theorem exists_embedding {K : Type} [Field K] [CharZero K] [Countable K] (ρ : K) (hρ : ρ ^ 2 = -(H.d : K)) :
    ∃ σ : K →+* ℂ, σ ρ = H.rt0 := by
  obtain ⟨σ⟩ := GlobalTheory.KeyRuleUnique.nonempty_ringHom_complex K
  have h : σ ρ ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, hρ, map_neg, map_natCast, H.sqrt_neg_disc_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact ⟨σ, h⟩
  · refine ⟨(starRingEnd ℂ).comp σ, ?_⟩
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h₁ := congrArg Complex.re H.sqrt_neg_disc_sq
    have h₂ := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [sq] at h₁ h₂
    have hre : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at h₁
      nlinarith [mul_self_nonneg H.rt0.re]
    rw [RingHom.comp_apply, h]
    apply Complex.ext <;> simp [hre]

theorem exists_datum_tate {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (T : GlobalTheory.CM.PAT H (Sp Ω)) (hg : 1 ≤ T.g)
    (ρ : Ω) (hρ : ρ ^ 2 = -(H.d : Ω)) (p q : ℕ)
    (hty : ∀ τ : 𝓞 E →+* Ω, (τ H.rt = ρ → LieMult T.t.act (𝟙 (Sp Ω)) τ p) ∧ (τ H.rt ≠ ρ → LieMult T.t.act (𝟙 (Sp Ω)) τ q)) :
    ∃ D : Datum H, D.p = p ∧ D.q = q ∧ 1 ≤ p + q ∧
      Nonempty (TateIso D Ω (Over.mk (𝟙 (Sp Ω)) ⟶ T.t.G) (fun a g => g ≫ T.t.act.act a)
        (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))) := by
  have hL := GlobalTheory.firstFiveLaws.1
  obtain ⟨K₀, T₀, φ, hc, hK, hgg, hG, hiso, hact⟩ := exists_pat_descent T
  obtain ⟨ρ₀, hρ₀, hρ₁⟩ : ∃ ρ₀ : K₀, ρ₀ ^ 2 = -(H.d : K₀) ∧ K₀.subtype ρ₀ = ρ := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-(H.d : K₀)) two_pos
    have h : K₀.subtype z ^ 2 = ρ ^ 2 := by rw [← map_pow, hz, map_neg, map_natCast, hρ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
    · exact ⟨z, hz, h⟩
    · exact ⟨-z, by rw [neg_sq, hz], by rw [map_neg, h, neg_neg]⟩
  obtain ⟨σ, hσ⟩ := exists_embedding ρ₀ hρ₀
  obtain ⟨T₁, m, hg₁⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap σ) T₀
  have hsm := T₀.ab.smooth
  have hm : LBIso T₁.t.PP.L (T₀.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have sq : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B), spMap f ≫ 𝟙 _ = 𝟙 _ ≫ spMap f := fun f => by simp
  have key : ∀ (τ : 𝓞 E →+* K₀) (n : ℕ), LieMult T₁.t.act (𝟙 _) (σ.comp τ) n ↔
      LieMult T.t.act (𝟙 _) (K₀.subtype.comp τ) n := fun τ n => by
    rw [GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ T₀.t.act T₁.t.act m.cart m.act,
      GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ T₀.t.act T.t.act hG hact, ← sq, ← sq,
      GlobalTheory.DetExtend.lieMult_extend, GlobalTheory.DetExtend.lieMult_extend]
  obtain ⟨D, hp, hq, hpq, ⟨I₁⟩⟩ := exists_datum_tate_complex T₁ (by omega) p q fun τ => by
    obtain ⟨τ₀, rfl⟩ := GlobalTheory.DetExtend.exists_factor σ τ
    rw [key, key, ← hσ, RingHom.comp_apply]
    have := hty (K₀.subtype.comp τ₀)
    rw [← hρ₁, RingHom.comp_apply] at this
    exact ⟨fun h => this.1 (congrArg _ (σ.injective h)), fun h => this.2 fun h' => h (congrArg _ (K₀.subtype.injective h'))⟩
  refine ⟨D, hp, hq, hpq, ?_⟩
  obtain ⟨I₂, -⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) T₀.t.PP.isLB T₁.t.PP.isLB m.cart hm T₀.t.act.act T₁.t.act.act m.act
    _ _ (sq σ)).1 I₁
  obtain ⟨I₃, -⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T₀.pol T₀.t.act.act K₀ ℂ σ (𝟙 _)).2 I₂ T₀.t.act.hom
  obtain ⟨I₄, -⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T₀.pol T₀.t.act.act K₀ Ω K₀.subtype (𝟙 _)).1 I₃
  obtain ⟨I₅, -⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) T₀.t.PP.isLB T.t.PP.isLB hG hiso T₀.t.act.act T.t.act.act hact
    _ _ (sq K₀.subtype)).2 I₄
  exact ⟨I₅⟩

end PositivityTheory.HtPt.Kftwo
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_finset_point {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {Z : Scheme.{0}} (p : Z ⟶ Sp K)
    [LocallyOfFinitePresentation p] (x : Sp Ω ⟶ Z) (hx : x ≫ p = spMap (algebraMap K Ω)) :
    ∃ S : Finset Ω, ∀ K' : IntermediateField K Ω, (S : Set Ω) ⊆ K' →
      ∃ y : Sp K' ⟶ Z, spMap K'.val.toRingHom ≫ y = x := by
  obtain ⟨R, ψ, ⟨S, rfl⟩, -, h⟩ := GlobalTheory.Spread.exists_fg_comp_eq (A := Ω) (𝟙 (Sp K)) p (pullback.snd _ _ ≫ x) (by
    rw [Category.assoc, hx, pullback.condition])
  refine ⟨S, fun K' hS => ?_⟩
  have hle : Algebra.adjoin K (S : Set Ω) ≤ K'.toSubalgebra := Algebra.adjoin_le hS
  let g : Algebra.adjoin K (S : Set Ω) →+* K' := (Subalgebra.inclusion hle).toRingHom
  refine ⟨spMap g ≫ inv (pullback.snd (𝟙 (Sp K)) _) ≫ ψ, ?_⟩
  have e : spMap K'.val.toRingHom ≫ spMap g = spMap (Algebra.adjoin K (S : Set Ω)).val.toRingHom :=
    (Spec.map_comp _ _).symm
  rw [← cancel_epi (pullback.snd (𝟙 (Sp K)) (spMap (algebraMap K Ω))), ← h, ← Category.assoc (spMap _), e,
    ← Category.assoc, ← GlobalTheory.Spread.bcMap_snd, Category.assoc, IsIso.hom_inv_id_assoc]

theorem exists_coeff_embedding {l : Level H} (c : Coeff l) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (ρ : Ω)
    (hρ : ρ ^ 2 = -(H.d : Ω)) : ∃ β : c.F →+* Ω, β (IntermediateField.inclusion c.le (baseKA l).ρ) = ρ := by
  have := c.fin
  set r : c.F := IntermediateField.inclusion c.le (baseKA l).ρ with hr
  have hr2 : r ^ 2 = -(H.d : c.F) := by rw [hr, ← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hd : (0 : ℚ) < H.d := by exact_mod_cast H.d_prime.pos
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ))) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => by nlinarith [sq_nonneg b]
  have hmin : Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ)) = minpoly ℚ r :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hr2]) (Polynomial.monic_X_pow_sub_C _ two_ne_zero)
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval (F := ℚ) (E := c.F) (K := Ω)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) (x := r) (y := ρ) (by rw [← hmin]; simp [hρ])
  exact ⟨φ.toRingHom, hφ⟩

theorem exists_point {D : Datum H} {l : Level H} (hA : l.A = 1) (Xo : Moduli D l) (c : Coeff l) {K : Type} [Field K]
    [CharZero K] (T : GlobalTheory.CM.PAT H (Sp K)) (ρ : AlgebraicClosure K) (hρ : ρ ^ 2 = -(H.d : AlgebraicClosure K))
    (hdet : DetCond D T.t.act (spMap (algebraMap K (AlgebraicClosure K))) ρ)
    (I : TateIso D (AlgebraicClosure K) (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G)
      (fun a g => g ≫ T.t.act.act a) (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))) :
    ∃ (K' : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K K') (y : Sp K' ⟶ Xo.XF c)
      (t' : SAB H (Sp K')), Nonempty (SABMap t' T.t (spMap (algebraMap K K'))) ∧
        Nonempty (SABMap t' Xo.univ.t (y ≫ pullback.fst _ _)) := by
  classical
  have hL := GlobalTheory.firstFiveLaws.1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have := c.fin
  have hsm := T.ab.smooth
  obtain ⟨β, hβ⟩ := exists_coeff_embedding c ρ hρ
  have hcard := (hL.mulN _ T.pol l.M hM).2.2.2.2 _ (spMap (algebraMap K (AlgebraicClosure K))) (Nat.cast_ne_zero.2 hM.ne')
  have hfin : Finite {x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G // x ^ l.M = 1} :=
    Nat.finite_of_card_ne_zero (by erw [hcard]; positivity)
  choose S hS using fun x : {x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G // x ^ l.M = 1} =>
    exists_finset_point T.t.G.hom x.1.left (Over.w x.1)
  let b := Module.finBasis ℚ c.F
  let U : Set (AlgebraicClosure K) := (⋃ x, (S x : Set (AlgebraicClosure K))) ∪ Set.range fun i => β (b i)
  have hU : Finite U := ((Set.finite_iUnion fun x => (S x).finite_toSet).union (Set.finite_range _)).to_subtype
  let K' := IntermediateField.adjoin K U
  have hfd : FiniteDimensional K K' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hβm : ∀ z, β z ∈ K' := fun z => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr z, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin K U (Or.inr ⟨i, rfl⟩))
  let β' : c.F →+* K' := β.codRestrict K' hβm
  let i : K' →+* AlgebraicClosure K := K'.val.toRingHom
  have hi : spMap (algebraMap K (AlgebraicClosure K)) = spMap i ≫ spMap (algebraMap K K') :=
    Spec.map_comp (CommRingCat.ofHom (algebraMap K K')) (CommRingCat.ofHom i)
  obtain ⟨T', m, -⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (algebraMap K K')) T
  have hm : LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨I', -, hI'⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) T.t.PP.isLB T'.t.PP.isLB m.cart hm T.t.act.act T'.t.act.act m.act
    _ _ hi).2 I
  have hdet' : DetCond D T'.t.act (spMap i) ρ := (GlobalTheory.PELDesc.detCond_pull m.cart _ _ m.act _ _ hi ρ).2 hdet
  have hepi : Epi (spMap i) :=
    have := GlobalTheory.FieldBaseChange.flat_spMap i
    have := GlobalTheory.FieldBaseChange.surjective_spMap i
    Flat.epi_of_flat_of_surjective _
  have hex : ∀ a, ∃ e : 𝟙_ (Over (Sp K')) ⟶ T'.t.G, toUnit (Over.mk (spMap i)) ≫ e = I'.ev l.M a := fun a => by
    obtain ⟨y, hy⟩ := hS ⟨I.ev l.M a, (I.onto _ hM _).2 ⟨a, rfl⟩⟩ K' fun z hz =>
      IntermediateField.subset_adjoin K U (Or.inl (Set.mem_iUnion.2 ⟨_, hz⟩))
    replace hy : spMap i ≫ y = (I.ev l.M a).left := hy
    have w : y ≫ T.t.G.hom = 𝟙 _ ≫ spMap (algebraMap K K') := by
      rw [← cancel_epi (spMap i), ← Category.assoc, hy, Category.id_comp, ← hi]
      exact Over.w (I.ev l.M a)
    refine ⟨Over.homMk (m.cart.1.lift y _ w) (m.cart.1.lift_snd _ _ _), Over.OverMorphism.ext ?_⟩
    rw [Over.comp_left, Over.toUnit_left]
    show spMap i ≫ m.cart.1.lift y _ w = _
    refine m.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, hy]
      exact hI' _ _
    · rw [Category.assoc, IsPullback.lift_snd, Category.comp_id]
      exact (Over.w (I'.ev l.M a)).symm
  choose e he using hex
  have inj := GlobalTheory.HeckePoint.toUnit_comp_injective (spMap i) T'.t.G
  obtain ⟨u, hu, π, hπ, huπ⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have hη : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      I'.ev l.M (π • a) = I'.ev l.M a := fun a h => by
    conv_rhs => rw [← one_smul (𝓞 E) a, ← huπ, add_smul, I'.add,
      (I'.ker _ hM _).2 (GlobalTheory.UnifObj.exists_smul_eq l.prod hu h), _root_.one_mul]
  let κ : KA l →+* K' := β'.comp (IntermediateField.inclusion c.le).toRingHom
  have hsm' := T'.ab.smooth
  let o : Obj D l (baseKA l) (spMap κ) :=
    { t := T'.t
      proper := T'.ab.proper
      ample := T'.ample
      ktriv := T'.ktriv
      eta := fun a => e (π • a)
      eta_add := fun a c => inj (by
        show toUnit _ ≫ _ = toUnit _ ≫ _
        rw [MonObj.comp_mul, he, he, he, smul_add, I'.add])
      eta_ker := fun a h => inj (by
        show toUnit _ ≫ _ = toUnit _ ≫ _
        rw [MonObj.comp_one, he]
        exact (I'.ker _ hM _).2 (GlobalTheory.UnifObj.exists_smul_eq ((mul_comm _ _).trans l.prod) hπ h))
      etaA := fun _ => 1
      etaA_add := fun _ _ => (_root_.mul_one _).symm
      etaA_ker := fun _ => rfl
      geom := fun k _ _ x δ hx => by
        obtain ⟨φ, rfl⟩ : ∃ φ : K' →+* k, x = spMap φ := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
        obtain rfl : φ.comp κ = δ :=
          congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
        obtain ⟨ψ, rfl⟩ : ∃ ψ : AlgebraicClosure K →+* k, ψ.comp i = φ := by
          letI := φ.toAlgebra
          set_option synthInstance.maxHeartbeats 400000 in
          exact ⟨(IsAlgClosed.lift (R := K') (S := AlgebraicClosure K) (M := k)).toRingHom,
            RingHom.ext fun z => (IsAlgClosed.lift (R := K') (S := AlgebraicClosure K) (M := k)).commutes z⟩
        have hx' : spMap (ψ.comp i) = spMap ψ ≫ spMap i := Spec.map_comp (CommRingCat.ofHom i) (CommRingCat.ofHom ψ)
        rw [hx']
        obtain ⟨J, hJ⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T'.pol T'.t.act.act _ k ψ (spMap i)).1 I'
        refine ⟨?_, J, ?_, fun a => ?_, fun a h => ?_⟩
        · have := (GlobalTheory.detCond_iff_of_field_extension E H D _ T'.t.G _ k ψ (spMap i) T'.t.act ρ hsm').2 hdet'
          rw [← hβ] at this
          exact this
        · have h₁ := J.ζ_prim _ l.A_pos
          have h₂ := (baseKA l).ζ_prim
          rw [hA, IsPrimitiveRoot.one_right_iff] at h₁ h₂
          rw [hA, h₁, h₂, map_one, Units.val_one]
        · rw [hA, MonObj.comp_one]
          exact ((J.ker 1 one_pos a).2 ⟨a, (one_smul _ _).symm⟩).symm
        · refine Eq.trans ?_ ((hJ _ hM).2 a).symm
          rw [← hη a h, ← he, ← Category.assoc]
          exact congrArg (· ≫ e (π • a)) (toUnit_unique _ _) }
  obtain ⟨f, ⟨hf, ⟨n⟩⟩, -⟩ := Xo.rep _ (spMap κ) inferInstance o
  have hκ : f ≫ Xo.s = spMap β' ≫ spMap (IntermediateField.inclusion c.le).toRingHom :=
    hf.trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom β'))
  refine ⟨K', hfd, pullback.lift f _ hκ, T'.t, ⟨m⟩, ?_⟩
  rw [pullback.lift_fst]
  exact ⟨n.toSABMap⟩

end PositivityTheory.HtPt.Kftwo
end
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix

namespace PositivityTheory.HtPt.Qak

theorem exists_pairEquiv {ι κ : Type} (e : ι ≃ κ) (m : κ → ℕ) (n : ι → ℕ) (h : ∀ s, m (e s) = n s) :
    ∃ g : (Σ τ, {p : Fin (m τ) × Fin (m τ) // p.1 < p.2}) ≃ (Σ s, {lk : Fin (n s) × Fin (n s) // lk.2 < lk.1}),
      ∀ (s : ι) (i j : Fin (m (e s))) (hij : i < j),
        g ⟨e s, ⟨(i, j), hij⟩⟩ = ⟨s, ⟨(Fin.cast (h s) j, Fin.cast (h s) i), hij⟩⟩ := by
  let e1 : (Σ s, {p : Fin (m (e s)) × Fin (m (e s)) // p.1 < p.2}) ≃ (Σ τ, {p : Fin (m τ) × Fin (m τ) // p.1 < p.2}) :=
    Equiv.sigmaCongrLeft (β := fun τ => {p : Fin (m τ) × Fin (m τ) // p.1 < p.2}) e
  let e2 : ∀ s, {p : Fin (m (e s)) × Fin (m (e s)) // p.1 < p.2} ≃ {lk : Fin (n s) × Fin (n s) // lk.2 < lk.1} := fun s =>
    { toFun := fun p => ⟨(Fin.cast (h s) p.1.2, Fin.cast (h s) p.1.1), p.2⟩
      invFun := fun p => ⟨(Fin.cast (h s).symm p.1.2, Fin.cast (h s).symm p.1.1), p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨e1.symm.trans (Equiv.sigmaCongrRight e2), fun s i j hij => ?_⟩
  have h1 : e1.symm ⟨e s, ⟨(i, j), hij⟩⟩ = ⟨s, ⟨(i, j), hij⟩⟩ := e1.symm_apply_apply ⟨s, ⟨(i, j), hij⟩⟩
  rw [Equiv.trans_apply, h1]
  rfl

theorem reindex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K L : Type) [Field K] [Field L] [Algebra K L] (v : ∀ s : CMType H ⊕ CMType H, Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) L), AlgebraicIndependent K (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) → ∃ T : FlagVar Dw → L, AlgebraicIndependent K T ∧ Set.range T = Set.range (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ ∀ (s : CMType H ⊕ CMType H) (i j : Fin (Dw.mult (Small.labelC s))) (hij : i < j), T ⟨Small.labelC s, ⟨(i, j), hij⟩⟩ = v s (Fin.cast (Small.mult_labelC Dw s) j) (Fin.cast (Small.mult_labelC Dw s) i) := by
  intro E _ _ _ H Dw K L _ _ _ v hv
  obtain ⟨g, hg⟩ := exists_pairEquiv (Small.labelEquiv H) Dw.mult (labelRk Dw) (Small.mult_labelC Dw)
  refine ⟨(fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∘ g,
    hv.comp g g.injective, g.surjective.range_comp _, fun s i j hij => ?_⟩
  exact congrArg (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)
    (hg s i j hij)

end PositivityTheory.HtPt.Qak
end
