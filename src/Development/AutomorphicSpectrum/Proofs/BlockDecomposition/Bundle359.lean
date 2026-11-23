module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle328
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Mathlib.RepresentationTheory.Character
public import Development.AbelianVarietyTheory.Counterexamples.SubgroupCharacterSums.SumSubgroupEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrrCharEqOneOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle999
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ThickeningIdealNilpotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle146
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle127
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMPull
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle346
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle327
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibOrd.ChainFilt

section generic
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

def subMap (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v)) (S : Subrepresentation ρ) :
    Subrepresentation σ :=
  ⟨S.toSubmodule.map f, by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, S.apply_mem_toSubmodule g hv, hf g v⟩⟩

theorem subMap_mono (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v))
    {S T : Subrepresentation ρ} (h : S ≤ T) : subMap f hf S ≤ subMap f hf T := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

theorem subMap_bot (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v)) :
    subMap f hf (⊥ : Subrepresentation ρ) = ⊥ :=
  Subrepresentation.toSubmodule_injective (Submodule.map_bot f)

theorem subQuot_subMap_equiv (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v))
    (hi : Function.Injective f) (S T : Subrepresentation ρ) :
    Nonempty ((subQuot S T).Equiv (subQuot (subMap f hf S) (subMap f hf T))) := by
  let e : S.toSubmodule ≃ₗ[ℂ] (subMap f hf S).toSubmodule :=
    Submodule.equivMapOfInjective f hi S.toSubmodule
  have he : (T.toSubmodule.comap S.toSubmodule.subtype).map e.toLinearMap =
      (subMap f hf T).toSubmodule.comap (subMap f hf S).toSubmodule.subtype := by
    ext ⟨w, hw⟩
    constructor
    · rintro ⟨⟨v, hvS⟩, hvT, hv⟩
      have hv' : f v = w := congrArg Subtype.val hv
      exact ⟨v, hvT, hv'⟩
    · rintro ⟨v, hvT, hv⟩
      obtain ⟨u, hu, rfl⟩ := hw
      have huv : v = u := hi hv
      subst huv
      exact ⟨⟨v, hu⟩, hvT, Subtype.ext rfl⟩
  let q := Submodule.Quotient.equiv _ _ e he
  refine ⟨Representation.Equiv.mk q fun g => ?_⟩
  refine Submodule.linearMap_qext _ ?_
  ext v
  show Submodule.Quotient.mk (e ⟨ρ g v.1, S.apply_mem_toSubmodule g v.2⟩) =
    Submodule.Quotient.mk (⟨σ g (f v.1), (subMap f hf S).apply_mem_toSubmodule g ⟨v.1, v.2, rfl⟩⟩ : _)
  congr 1
  exact Subtype.ext (hf g v.1)

end generic

section chain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {R : ℕ → GRep k n → Prop} {Z : ℕ → Prop}

theorem chain_le {a b : ℕ} {X : GRep k n} (h : Chain R Z a b X) : a ≤ b := by
  induction h <;> omega

theorem filt_extend {a b : ℕ} {X Y : GRep k n} (f : Y.V →ₗ[ℂ] X.V)
    (hf : ∀ x v, f (Y.ρ x v) = X.ρ x (f v)) (hi : Function.Injective f) (hab : a < b)
    (F' : ℕ → Subrepresentation Y.ρ) (hanti : Antitone F') (htop : F' (a + 1) = ⊤) (hbot : F' b = ⊥)
    (hst : ∀ i, a + 1 ≤ i → i < b →
      (∃ A, R i A ∧ Nonempty ((subQuot (F' i) (F' (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F' i = F' (i + 1)))
    (h0 : (∃ A, R a A ∧ Nonempty ((subQuot ⊤ (subMap f hf ⊤)).Equiv A.ρ)) ∨
      (Z a ∧ (⊤ : Subrepresentation X.ρ) = subMap f hf ⊤)) :
    ∃ F : ℕ → Subrepresentation X.ρ, Antitone F ∧ F a = ⊤ ∧ F b = ⊥ ∧ ∀ i, a ≤ i → i < b →
      (∃ A, R i A ∧ Nonempty ((subQuot (F i) (F (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F i = F (i + 1)) := by
  classical
  obtain ⟨F, hF1, hF2⟩ : ∃ F : ℕ → Subrepresentation X.ρ, (∀ i, i ≤ a → F i = ⊤) ∧
      (∀ i, a < i → F i = subMap f hf (F' i)) :=
    ⟨fun i => if i ≤ a then ⊤ else subMap f hf (F' i), fun i h => if_pos h,
      fun i h => if_neg (by omega)⟩
  refine ⟨F, ?_, hF1 a le_rfl, ?_, ?_⟩
  · intro i j hij
    by_cases h2 : i ≤ a
    · rw [hF1 i h2]; exact le_top
    · rw [hF2 i (by omega), hF2 j (by omega)]; exact subMap_mono f hf (hanti hij)
  · rw [hF2 b hab, hbot, subMap_bot]
  · intro i hai hib
    rcases hai.eq_or_lt with rfl | hlt
    · rw [hF1 a le_rfl, hF2 (a + 1) (by omega), htop]
      exact h0
    · rw [hF2 i hlt, hF2 (i + 1) (by omega)]
      rcases hst i hlt hib with ⟨A, hR, ⟨e⟩⟩ | ⟨hZ, he⟩
      · obtain ⟨e'⟩ := subQuot_subMap_equiv f hf hi (F' i) (F' (i + 1))
        exact Or.inl ⟨A, hR, ⟨e'.symm.trans e⟩⟩
      · exact Or.inr ⟨hZ, by rw [he]⟩

theorem exists_filtration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (R : ℕ → GRep k n → Prop) (Z : ℕ → Prop) (a b : ℕ)
    (X : GRep k n), Chain R Z a b X → ∃ F : ℕ → Subrepresentation X.ρ, Antitone F ∧ F a = ⊤ ∧
      F b = ⊥ ∧ ∀ i, a ≤ i → i < b →
        (∃ A, R i A ∧ Nonempty ((subQuot (F i) (F (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F i = F (i + 1)) := by
  intro k _ _ _ _ n R Z a b X h
  induction h with
  | nil a X hs =>
    refine ⟨fun _ => ⊥, fun _ _ _ => le_rfl, ?_, rfl, fun i h1 h2 => by omega⟩
    refine Subrepresentation.toSubmodule_injective ?_
    ext v
    have : v = 0 := Subsingleton.elim _ _
    subst this
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  | @step a b X Y A hR hs hc ih =>
    obtain ⟨f, g, hf, hg, hi, hsur, he⟩ := hs
    obtain ⟨F', h1, h2, h3, h4⟩ := ih
    have hab := chain_le hc
    refine filt_extend f hf hi (by omega) F' h1 h2 h3 h4 (Or.inl ⟨A, hR, ?_⟩)
    obtain ⟨S, hS, e⟩ := GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv X.ρ A.ρ
      ⟨g, fun x => LinearMap.ext (hg x)⟩ hsur
    have hS' : S = subMap f hf ⊤ := by
      refine Subrepresentation.toSubmodule_injective ?_
      refine hS.trans ?_
      show LinearMap.ker g = Submodule.map f ⊤
      rw [Submodule.map_top, he]
    exact hS' ▸ e
  | @skip a b X Y hZ he hc ih =>
    obtain ⟨e⟩ := he
    obtain ⟨F', h1, h2, h3, h4⟩ := ih
    have hab := chain_le hc
    refine filt_extend e.toLinearEquiv.toLinearMap (eint e) e.toLinearEquiv.injective (by omega)
      F' h1 h2 h3 h4 (Or.inr ⟨hZ, ?_⟩)
    refine Subrepresentation.toSubmodule_injective ?_
    show ⊤ = Submodule.map e.toLinearEquiv.toLinearMap ⊤
    rw [Submodule.map_top, LinearEquiv.range]

end chain

end GlobalTheory.CompanionTheory.LeibOrd.ChainFilt

end
end

section

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

namespace GlobalTheory.CompanionTheory.TyFin

section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem isCuspChar_character {d : ℕ} (τ : FDRep ℂ (GL (Fin d) K)) (hs : Simple τ) (hc : IsCuspidal K τ) :
    CuspElliptic.IsCuspChar τ.character := by
  rw [GlobalTheory.CuspCharCheck.isCuspChar_iff]
  refine ⟨τ, hs, rfl, fun a h0 h1 v hv => ?_⟩
  refine hc 2 (twoBlock d a) ?_ le_rfl v fun u hu => hv u ?_
  · intro c
    fin_cases c
    · exact ⟨⟨0, by omega⟩, by simp [twoBlock, h0]⟩
    · exact ⟨⟨a, h1⟩, by simp [twoBlock]⟩
  · intro i j
    by_cases hij : i.val < a ∧ a ≤ j.val
    · exact Or.inr hij
    · left
      by_cases hb : twoBlock d a i = twoBlock d a j
      · exact hu.2 i j hb
      · have hi : a ≤ i.val := by
          by_contra hi
          have hj : j.val < a := by
            by_contra hj
            exact hij ⟨by omega, by omega⟩
          exact hb (by simp [twoBlock, show i.val < a by omega, hj])
        have hj : j.val < a := by
          by_contra hj
          exact hb (by simp [twoBlock, show ¬ i.val < a by omega, show ¬ j.val < a by omega])
        have hne : i ≠ j := fun e => by subst e; omega
        rw [if_neg hne]
        exact hu.1.1 i j (by simp [twoBlock, show ¬ i.val < a by omega, hj])

theorem finrank_of_simple_cuspidal (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) {d : ℕ} (hd : 1 ≤ d)
    (τ : FDRep ℂ (GL (Fin d) K)) (hs : Simple τ) (hc : IsCuspidal K τ) :
    (Module.finrank ℂ τ : ℤ) = ∏ i ∈ Finset.Ico 1 d, ((q K : ℤ) ^ i - 1) := by
  have h := isCuspChar_character τ hs hc
  obtain ⟨k, -, hk⟩ := GlobalTheory.CuspFormula.exists_regular K θ hθ d hd τ.character
    (GlobalTheory.CuspGL.isIrrChar_of_norm_one _ h.1) (GlobalTheory.CuspGL.isPrimitive_of_isCuspChar _ h)
  have h1 := hk 1
  have hid : Matrix.toLin' ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    simp [Module.End.one_eq_id]
  have hfr : Module.finrank K (Fin d → K) = d := by simp
  rw [FDRep.char_one, hid, GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico K (Fin d → K) (GlobalTheory.CuspGL.rootSum θ k) (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow K θ k).2
    (by rw [hfr]; omega), hfr, Nat.card_eq_fintype_card] at h1
  have hsign : ((-1 : ℂ)) ^ (d - 1) * ∏ i ∈ Finset.Ico 1 d, (1 - (Fintype.card K : ℂ) ^ i) =
      ∏ i ∈ Finset.Ico 1 d, ((Fintype.card K : ℂ) ^ i - 1) := by
    rw [← Nat.card_Ico 1 d, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [hsign] at h1
  have h2 : ((Module.finrank ℂ τ : ℤ) : ℂ) = ((∏ i ∈ Finset.Ico 1 d, ((q K : ℤ) ^ i - 1) : ℤ) : ℂ) := by
    push_cast
    exact h1
  exact_mod_cast h2

end

end GlobalTheory.CompanionTheory.TyFin
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso GlobalTheory.CompanionTheory.DisoHm

noncomputable section
namespace GlobalTheory.CompanionTheory.DisoHm
section Cmp
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem ev_base {W : X.Opens} (T : Thick (nlFun γ p X q κ)) (h : InU W T) (a : O) (r : R)
    (hr : κ a = Ideal.Quotient.mk I r) : ev T h (strV q W a) = Ideal.Quotient.mk T.J (T.i r) := by
  have e := evalAt_base q κ (show PtOver X q κ (T.B ⧸ T.J) from T.y).1.1 (pt T)
    (show PtOver X q κ (T.B ⧸ T.J) from T.y).2 h a
  refine e.trans ?_
  rw [hr]
  exact T.w r

theorem quot_eq_id {W : X.Opens} {d : ℕ} (c : Chart γ p q κ W d) (hW : IsAffineOpen W)
    (θ : c.D.B ⧸ c.D.J →+* c.D.B ⧸ c.D.J)
    (h1 : ∀ r, θ (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (c.D.i r))
    (h2 : ∀ f, θ (ev c.D c.inV f) = ev c.D c.inV f) : θ = RingHom.id _ := by
  have key : ∀ θ' : c.D.B ⧸ c.D.J →+* c.D.B ⧸ c.D.J,
      (∀ r, θ' (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (c.D.i r)) →
      (∀ f, θ' (ev c.D c.inV f) = ev c.D c.inV f) →
      (ptFun X q κ).map (CommRingCat.ofHom θ') c.D.y = c.D.y := by
    intro θ' a b
    refine Subtype.ext (Prod.ext ?_ ?_)
    · refine RingHom.ext fun z => ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      have w := c.D.w r
      change θ' ((show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r)) =
        (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r)
      have w' : (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk _ (c.D.i r) := w
      rw [w']
      exact a r
    · change Spec.map (CommRingCat.ofHom θ') ≫ pt c.D = pt c.D
      have e : Spec.map (CommRingCat.ofHom (ev c.D c.inV)) ≫ hW.fromSpec = pt c.D :=
        GlobalTheory.CompanionTheory.ChartAlg.eq_specMap hW (pt c.D) c.inV
      have e2 : θ'.comp (ev c.D c.inV) = ev c.D c.inV := RingHom.ext b
      calc Spec.map (CommRingCat.ofHom θ') ≫ pt c.D
          = Spec.map (CommRingCat.ofHom θ') ≫ Spec.map (CommRingCat.ofHom (ev c.D c.inV)) ≫ hW.fromSpec := by rw [e]
        _ = Spec.map (CommRingCat.ofHom (θ'.comp (ev c.D c.inV))) ≫ hW.fromSpec := by
            rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        _ = pt c.D := by rw [e2, e]
  obtain ⟨g₀, -, hu⟩ := c.rep (CommRingCat.of (c.D.B ⧸ c.D.J)) c.D.y c.inV
  exact (hu _ (key θ h1 h2)).trans (hu _ (key _ (fun _ => rfl) (fun _ => rfl))).symm

end Cmp

theorem cmp_bij : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (m : ℕ)
    (cL : Chart (pdm h m) l q (κm l O m) W d)
    (hcL : ∀ i, ev cL.D cL.inV (c.t i) = Ideal.Quotient.mk _ (cL.t i))
    (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) W d),
    letI := (strV q W).toAlgebra
    ∀ (e : O ⊗[O] Γ(X, W) ≃+* cO.D.B), (∀ r, e (r ⊗ₜ 1) = cO.D.i r) → (∀ i, e (1 ⊗ₜ c.t i) = cO.t i) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f))) →
      ∀ (hT : Good (l := l) cO.D m) (σ : cL.D ⟶ GObj h cO.D m hT),
        (∀ i, σ.φ (cL.t i) = Ideal.Quotient.mk _ (cO.t i)) → Function.Bijective σ.φ := by
  intro l _ O _ X q h W d c m cL hcL cO
  letI := (strV q W).toAlgebra
  intro e he het hev hT σ hσ
  let E : Γ(X, W) ≃+* cO.D.B := (Algebra.TensorProduct.lid O Γ(X, W)).symm.toRingEquiv.trans e
  have hE : ∀ f, E f = e (1 ⊗ₜ f) := fun f => rfl
  have hEs : ∀ a, E (strV q W a) = cO.D.i a := fun a => by
    rw [hE, ← he]
    congr 1
    change (1 : O) ⊗ₜ[O] (algebraMap O Γ(X, W) a) = a ⊗ₜ 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hEt : ∀ i, E (c.t i) = cO.t i := het
  have hevE : ∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (E f) := hev
  let ψ : MvPolynomial (Fin d) O →+* cO.D.B := MvPolynomial.eval₂Hom cO.D.i cO.t
  have hψ : ψ.Etale := cO.etale
  let g : cO.D.B →+* cL.D.B ⧸ cL.D.J := (ev cL.D cL.inV).comp (E.symm : cO.D.B →+* Γ(X, W))
  let f₁ : MvPolynomial (Fin d) O →+* cL.D.B :=
    MvPolynomial.eval₂Hom (cL.D.i.comp (Ideal.Quotient.mk _)) cL.t
  have hg1 : ∀ f, g (E f) = ev cL.D cL.inV f := fun f => by
    change ev cL.D cL.inV (E.symm (E f)) = _
    rw [RingEquiv.symm_apply_apply]
  have hc : g.comp ψ = (Ideal.Quotient.mk cL.D.J).comp f₁ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · have e1 : ψ (MvPolynomial.C a) = E (strV q W a) := by
        rw [hEs]; simp [ψ]
      have e2 : f₁ (MvPolynomial.C a) = cL.D.i (Ideal.Quotient.mk _ a) := by simp [f₁]
      change g (ψ (MvPolynomial.C a)) = Ideal.Quotient.mk cL.D.J (f₁ (MvPolynomial.C a))
      rw [e1, e2, hg1]
      exact ev_base cL.D cL.inV a _ rfl
    · have e1 : ψ (MvPolynomial.X i) = E (c.t i) := by
        rw [hEt]; simp [ψ]
      have e2 : f₁ (MvPolynomial.X i) = cL.t i := by simp [f₁]
      change g (ψ (MvPolynomial.X i)) = Ideal.Quotient.mk cL.D.J (f₁ (MvPolynomial.X i))
      rw [e1, e2, hg1]
      exact hcL i
  obtain ⟨H, ⟨hH1, hH2⟩, -⟩ := GlobalTheory.T.etale_lifting_of_nil_ideal cL.D.J (GlobalTheory.CompanionTheory.ChartMaps.nil_J cL.D) _ _ ψ hψ f₁ g hc
  have hHi : ∀ a, H (cO.D.i a) = cL.D.i (Ideal.Quotient.mk _ a) := fun a => by
    have := RingHom.congr_fun hH1 (MvPolynomial.C a)
    simpa [ψ, f₁] using this
  have hHt : ∀ i, H (cO.t i) = cL.t i := fun i => by
    have := RingHom.congr_fun hH1 (MvPolynomial.X i)
    simpa [ψ, f₁] using this
  have hHe : ∀ f, Ideal.Quotient.mk cL.D.J (H (E f)) = ev cL.D cL.inV f := fun f => by
    rw [← hg1, ← hH2]
    rfl
  have hk : ∀ a ∈ lm (l := l) cO.D m, H a = 0 := by
    have hle : lm (l := l) cO.D m ≤ RingHom.ker H := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      change H ((l : cO.D.B) ^ m) = 0
      have e1 : (l : cO.D.B) ^ m = cO.D.i ((l : O) ^ m) := by
        rw [map_pow, map_natCast]
      rw [e1, hHi, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
    exact fun a ha => hle ha
  let Hb : GB (l := l) cO.D m →+* cL.D.B := Ideal.Quotient.lift _ H hk
  have hHb : ∀ x, Hb (Ideal.Quotient.mk _ x) = H x := fun x => Ideal.Quotient.lift_mk _ H hk
  let mkG : cO.D.B →+* (GObj h cO.D m hT).B := Ideal.Quotient.mk (lm (l := l) cO.D m)
  have hV := inU_G h cO.D m hT cO.inV
  have hs : σ.φ.comp H = mkG := by
    have uniq := GlobalTheory.T.etale_lifting_of_nil_ideal (GObj h cO.D m hT).J (GlobalTheory.CompanionTheory.ChartMaps.nil_J (GObj h cO.D m hT)) _ _ ψ hψ
      (mkG.comp ψ) ((Ideal.Quotient.mk (GObj h cO.D m hT).J).comp mkG) rfl
    refine uniq.unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
    · refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · have e1 : ψ (MvPolynomial.C a) = cO.D.i a := by simp [ψ]
        change σ.φ (H (ψ (MvPolynomial.C a))) = mkG (ψ (MvPolynomial.C a))
        rw [e1, hHi, σ.comm]
        rfl
      · have e1 : ψ (MvPolynomial.X i) = cO.t i := by simp [ψ]
        change σ.φ (H (ψ (MvPolynomial.X i))) = mkG (ψ (MvPolynomial.X i))
        rw [e1, hHt, hσ]
        rfl
    · refine RingHom.ext fun x => ?_
      obtain ⟨f, rfl⟩ := E.surjective x
      have a1 := ev_G h cO.D m hT cO.inV hV f
      have a2 := ev_hom σ cL.inV hV f
      rw [hevE] at a1
      rw [← hHe] at a2
      exact a2.symm.trans a1
  have hs' : ∀ x, σ.φ (H x) = mkG x := fun x => RingHom.congr_fun hs x
  let ρ : cL.D.B →+* cL.D.B := Hb.comp σ.φ
  have hρH : ∀ x, ρ (H x) = H x := fun x => by
    change Hb (σ.φ (H x)) = H x
    rw [hs']
    exact hHb x
  have hρi : ∀ r, ρ (cL.D.i r) = cL.D.i r := fun r => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← hHi, hρH]
  have hρt : ∀ i, ρ (cL.t i) = cL.t i := fun i => by
    rw [← hHt, hρH]
  have hle : cL.D.J ≤ cL.D.J.comap ρ := by
    intro x hx
    have : cL.D.J ≤ cL.D.J.comap ρ := by
      conv_lhs => rw [cL.J_eq]
      refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
      rw [Ideal.mem_comap, Ideal.mem_comap, hρi, cL.J_eq]
      exact Ideal.mem_map_of_mem _ hr
    exact this hx
  have hθ : Ideal.quotientMap cL.D.J ρ hle = RingHom.id _ := by
    refine quot_eq_id cL c.affine _ (fun r => ?_) (fun f => ?_)
    · rw [Ideal.quotientMap_mk, hρi]
    · rw [← hHe, Ideal.quotientMap_mk, hρH]
  have hid : ρ = RingHom.id _ := by
    refine (GlobalTheory.CompanionTheory.ChartMaps.exists_unique_lift cL cL.D (RingHom.id _) (fun _ => rfl) cL.t (fun _ => rfl)).unique
      ⟨hρi, hρt, RingHom.ext fun x => ?_⟩ ⟨fun _ => rfl, fun _ => rfl, rfl⟩
    have := RingHom.congr_fun hθ (Ideal.Quotient.mk _ x)
    rw [Ideal.quotientMap_mk] at this
    exact this
  refine Function.bijective_iff_has_inverse.2 ⟨Hb, fun x => RingHom.congr_fun hid x, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) cO.D m from y)
  change σ.φ (Hb (Ideal.Quotient.mk _ x)) = _
  rw [hHb, hs']
  rfl

end GlobalTheory.CompanionTheory.DisoHm
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgGu

theorem rank_twJacquet_multiProd_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (ψ : AddChar k Circle) (hc : Continuous ψ)
    (h1 : ψ ≠ 1) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (hs : ∀ a, IsSmooth (π a))
    (hr : ∀ a, Module.rank ℂ (TwJacquet (π a) (unipB k (Fin (d a))) (whitChar ψ (d a))) ≤ 1) :
    Module.rank ℂ (TwJacquet (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  obtain ⟨e⟩ := hH ψ hc h1 h N d hd X π hs
  exact e.rank_eq.le.trans (GlobalTheory.T.tensor_product_rank_le_one _ hr)

theorem rank_twJacquet_prodIrr_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k →
    ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k))
      (hd : ∑ a, (x a).1 = N),
      Module.rank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  intro k _ _ _ _ hH hR ψ hc h1 h N x hd
  exact rank_twJacquet_multiProd_le_one hH ψ hc h1 h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V)
    (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)
    (fun a => hR ψ hc h1 (x a).1 (x a).2.rep.V (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)

end GlobalTheory.CompanionTheory.RgGu

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mirabolic_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), IsClosed (Mir k n : Set (GL (Fin (n + 1)) k)) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.MirClosed.isClosed_mirabolic | exact GlobalTheory.CompanionTheory.BZRes.MirClosed.isClosed_mirabolic | (intros; apply GlobalTheory.CompanionTheory.BZRes.MirClosed.isClosed_mirabolic <;> assumption)
end
