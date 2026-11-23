module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfGoodExtensions
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module

noncomputable section

namespace Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Module IsDiscreteValuationRing

section Hecke

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br Formalism.NG Formalism.NG.QuotientPowerLengths

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [Fintype X]
  {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)

theorem heckeEig_indep (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) :
    iSupIndep (heckeEig T act) := by
  let F : T → Module.End (FractionRing O) (TensorProduct O (FractionRing O) M) :=
    fun f => actK T act f
  have hc : ∀ f g, Commute (F f) (F g) := fun f g => by
    show actK T act f * actK T act g = actK T act g * actK T act f
    rw [← map_mul, mul_comm, map_mul]
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo F
    (fun f g φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc g f) φ)
  let χ : X → (T → FractionRing O) := fun x f => algebraMap O (FractionRing O) ((f : X → O) x)
  have hχ : Function.Injective χ := by
    intro x y hxy
    by_contra hne
    obtain ⟨f, hf, hfx⟩ := hsep x y hne
    exact hfx (IsFractionRing.injective O (FractionRing O) (congrFun hxy ⟨f, hf⟩))
  refine (h.comp hχ).mono fun x => iInf_mono fun f => ?_
  exact ((F f).genEigenspace _).monotone le_top

end Hecke

section Record

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br

variable {D : D7}

theorem eig_isCompl (i : D.nd.Loc) (S : Finset (D.nd.X i)) :
    IsCompl (D.nd.eigSum i ↑S) (D.nd.eigSum i (↑S)ᶜ) := by
  refine ⟨(heckeEig_indep (D.nd.T i) (D.nd.act i) (D.nd.T_sep i)).disjoint_biSup_biSup
    disjoint_compl_right, codisjoint_iff.2 ?_⟩
  rw [eq_top_iff, ← EigSpan_holds D.nd i]
  refine iSup_le fun x => ?_
  by_cases hx : x ∈ (S : Set (D.nd.X i))
  · exact le_sup_of_le_left (le_biSup (heckeEig (D.nd.T i) (D.nd.act i)) hx)
  · exact le_sup_of_le_right
      (le_biSup (heckeEig (D.nd.T i) (D.nd.act i)) (show x ∈ (S : Set (D.nd.X i))ᶜ from hx))

def prGood (i : D.nd.Loc) :
    Module.End (FractionRing (D.nd.O i))
      (TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)) :=
  (D.nd.eigSum i ↑(D.nd.Zgood i)).projection (D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ)
    (eig_isCompl i (D.nd.Zgood i))

end Record

section Reduce

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br Formalism.NG Formalism.NG.QuotientPowerLengths

variable {D : D7}

def EtaBound (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ c : D.nd.X i → ℚ,
    D.nd.etaLoc i ≤
      ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ) * (c π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard) ∧
    ∀ π ∈ D.nd.Zgood i, LocalCongruenceBound CT eta i ρ π (c π)

def CongruenceSingleEndomorphism (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (a : D.nd.X i → D.nd.O i) (c : D.nd.X i → ℚ),
    (∀ π ∈ D.nd.Zgood i, a π ≠ 0 ∧
      (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π,
        α.baseChange (FractionRing (D.nd.O i)) u = a π • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a π}) ≤
        c π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard ∧
      LocalCongruenceBound CT eta i ρ π (c π)) ∧
    ∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
      α.baseChange (FractionRing (D.nd.O i)) u = 0

def CongruenceFamilyEndomorphisms (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ (E : Set (Module.End (D.nd.O i) (D.nd.Mt i))) (a : D.nd.X i → D.nd.O i) (c : D.nd.X i → ℚ),
    (∀ α ∈ E, (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      ∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
    ∀ π ∈ D.nd.Zgood i, a π ≠ 0 ∧
      (∃ α ∈ E, ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π,
        α.baseChange (FractionRing (D.nd.O i)) u = a π • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a π}) ≤
        c π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard ∧
      LocalCongruenceBound CT eta i ρ π (c π)

open Classical in
def cutLocus (i : D.nd.Loc) (Xs : Set (D.nd.X i)) : Finset (D.nd.X i) :=
  Finset.univ.filter fun x => x ∈ D.nd.Z i ∨ x ∉ Xs

def vccCut (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i) : ℚ :=
  lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ ccAt (D.nd.T i) (cutLocus i Xs) π)

def CutAt (i : D.nd.Loc) (k : Fin 2) (π : D.nd.X i) (Xs : Set (D.nd.X i))
    (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i) : Prop :=
  π ∈ Xs ∧ π ∈ D.nd.Z i ∧ (∀ x ∈ Xs, x ∈ D.nd.Z i → x ∈ D.nd.Zgood i) ∧
    (∀ f : D.nd.T i, β * D.nd.act i f = D.nd.act i f * β) ∧ b ≠ 0 ∧
    (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, β.baseChange (FractionRing (D.nd.O i)) u = b • u) ∧
    (∀ x, x ∉ Xs → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
      β.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
    lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {b}) ≤
      padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard

def CongruenceLocalDecomposition (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ (Xs : D.nd.X i → Set (D.nd.X i)) (β : D.nd.X i → Module.End (D.nd.O i) (D.nd.Mt i))
    (b : D.nd.X i → D.nd.O i),
    ∀ π ∈ D.nd.Zgood i, CutAt i k π (Xs π) (β π) (b π) ∧ LocalCongruenceBound CT eta i ρ π (vccCut i (Xs π) π)

end Reduce

end Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

def genA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ s : Finset (↥(GK K) → T₂.V),
      s.card ≤ 2 * ((finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 + 1) * r) ∧
      Submodule.span ↥(OL LL) (s : Set (↥(GK K) → T₂.V)) ⊔ latticeCoboundaries T₂.L = latticeFiniteCocycles (P.PD K) T₂.L

def liftA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ J : Finset ℤ, J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧ (0 : ℤ) ∉ J ∧
      F.LiftF (P.PD K) (expLift l h J)

def killA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ s h' : ℕ, finrank ↥(K0 K) ↥K.1 * s = l - 1 ∧ 1 ≤ h' ∧ h' ≤ h + S + 1 ∧
      ∃ s₀ : Finset (↥(GK K) → T₂.V),
        s₀.card ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 * (finrank ↥(K0 K) ↥K.1 + 1) * m ∧
        (s₀ : Set (↥(GK K) → T₂.V)) ⊆ latticeFiniteCocycles (P.PD K) T₂.L ∧
        ∀ p ∈ latticeFiniteCocycles (P.PD K) T₂.L,
          (l ^ YA l (finrank ↥(K0 K) ↥K.1) s h' S η : ℕ) • p ∈
            Submodule.span ↥(OL LL) (s₀ : Set (↥(GK K) → T₂.V)) ⊔ F.ImF (P.PD K)

theorem claimA_of_steps (hG : genA P K LL) (hL : liftA P K LL) (hK : killA P K LL) :
    claimA P K LL := by
  intro T₁ T₂ F r S η m h up b hH
  obtain ⟨s, hs, hgen⟩ := hG T₁ T₂ F r S η m h up b hH
  obtain ⟨J, hJ, h0, hlift⟩ := hL T₁ T₂ F r S η m h up b hH
  obtain ⟨σ, h', hes, hh', hle, s₀, hs₀, hsub, hkill⟩ := hK T₁ T₂ F r S η m h up b hH
  refine ⟨σ, h', s.card, J, hes, hh', hle, hJ, h0, hs, s, s₀, le_rfl, hgen, hs₀, hsub, hkill, ?_⟩
  intro p hp
  have hpZ : p ∈ latticeFiniteCocycles (P.PD K) T₂.L := (Submodule.span_le.mpr hsub) hp
  have h1 := hlift p hpZ
  have e1 : ((l ^ expLift l h J : ℕ) : ↥(OL LL)) =
      ((((P.PD K).p : ℕ) : ↥(OL LL))) ^ expLift l h J := by
    rw [P.PD_p K]; push_cast; rfl
  rw [← Nat.cast_smul_eq_nsmul ↥(OL LL), e1]
  exact h1

end Local

def genR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → genA (D.loc l) K LL

def liftR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → liftA (D.loc l) K LL

def killR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → killA (D.loc l) K LL

theorem local_form_of_three_inputs (D : D7) (hG : genR D) (hL : liftR D) (hK : killR D) : LocalTheoremAtGoodExtensions D :=
  fun l _ hl K LL hg =>
    claimA_of_steps (D.loc l) K LL (hG l hl K LL hg) (hL l hl K LL hg) (hK l hl K LL hg)

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def H0FixedPoints (W : LocWach PD LL O v n) : Prop :=
  ∀ T : LocLat G Qp LL O, Nonempty (↥(invariantLattice T) ≃ₗ[O] ↥(fixDD W T))

def FontCore (W : LocWach PD LL O v n) : Prop :=
  (∀ (T T' : LocLat G Qp LL O) (f : W.DD T →ₗ[W.EE] W.DD T'),
    (∀ x, f (W.φD T x) = W.φD T' (f x)) → (∀ g x, f (W.γD T g x) = W.γD T' g (f x)) →
      ∃! F : LatHom T.L T'.L, ∀ x, W.map F x = f x) ∧
  (∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := Qp) (O := O) ι π →
    Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧
      ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x) ∧
  (∃ ψ : W.EE →ₗ[O] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧
    (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧
    (∀ j < PD.p, ∀ a, ψ (algebraMap (LetA O n) W.EE (1 + letπ) ^ j * W.φE a) = if j = 0 then a else 0) ∧
    ∀ x, ∃ c : Fin PD.p → W.EE, x = ∑ j : Fin PD.p, algebraMap (LetA O n) W.EE (1 + letπ) ^ (j : ℕ) * W.φE (c j)) ∧
  ∀ T : LocLat G Qp LL O, ∃ ψ : W.DD T →ₗ[O] W.DD T, (∀ x, ψ (W.φD T x) = x) ∧
    (∀ (a : W.EE) x, ψ (W.φE a • x) = a • ψ x) ∧ ∀ g x, ψ (W.γD T g x) = W.γD T g (ψ x)

theorem herrLat_iff (W : LocWach PD LL O v n) : HerrLat W ↔
    (∀ T : LocLat G Qp LL O, Function.Surjective (W.clK T) ∧
      ∀ p, W.clK T p = 0 ↔ ∃ m : W.DD T, (∀ δ ∈ W.DelF, W.γD T δ m = m) ∧
        (p : W.DD T × W.DD T) = (W.φD T m - m, W.γD T W.gamK m - m)) ∧
    W.ClKNat ∧ H0FixedPoints W ∧ FontCore W := Iff.rfl

end Core

def H0InvariantsUnramified (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), H0FixedPoints ((HW l).W K 1 LL hA.2.2)

def FieldOfNormsSequence (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.HerrComplexNaturality.FN D HW F

def H0InvariantsTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FieldOfNormsSequence D HW F → H0InvariantsUnramified D HW F

def LitFont (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), FontCore ((HW l).W K 1 LL hA.2.2)

def HerrLatticeDescription (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm16 D HW F

def HerrLatticeHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F ∧ H0InvariantsUnramified D HW F ∧ LitFont D HW F

def HerrLatticeTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := HerrLatticeHypotheses D HW F → HerrLatticeDescription D HW F

theorem herr_lattice_of_fon (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrLatticeTheorem D HW F := by
  rintro ⟨h, h0, hF⟩ l _ K LL hA
  have h1 := (h l K 1 LL hA.2.2).1 (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hA.2.1)
  refine (herrLat_iff _).2 ⟨fun T => ⟨(h1 T).1, (h1 T).2.1⟩, ?_, h0 l K LL hA, hF l K LL hA⟩
  intro T T' f pr pr' hp
  exact ((h1 T).2.2 T' f pr pr' hp).symm

def LitSub (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), HerrSub ((HW l).W K 1 LL hA.2.2)

def HerrExtensionEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
    Formalism.MainNotions.tableLineDegreeTwo.HerrExt ((HW l).W K 1 LL hA.2.2) ((F l).E K 1 LL hA.2.2).tie

def HerrLatticeFurtherConditions (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm17 D HW F

theorem herr_lattice_rest_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrLatticeFurtherConditions D HW F ↔ LitSub D HW F ∧ HerrExtensionEtale D HW F :=
  ⟨fun H => ⟨fun l _ K LL hA => (H l K LL hA).1, fun l _ K LL hA => (H l K LL hA).2⟩,
    fun H l _ K LL hA => ⟨H.1 l K LL hA, H.2 l K LL hA⟩⟩

def SenOperatorLetter (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm21 D HW F

def SenOperatorTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.UnusedSlot35.AdmDss D HW F Cm → SenOperatorLetter D HW F

end Formalism.MainNotions.InvariantsGenerators
end
end

section

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {LL' O' : Type} [Field LL'] [Algebra Qp LL'] [TopologicalSpace LL'] [CommRing O'] [Algebra O' LL']
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem comp_inj {E : Type} [Field E] [Algebra Qp E] (ι : LL →ₐ[Qp] LL') :
    Function.Injective (fun τ : E →ₐ[Qp] LL => ι.comp τ) := by
  intro τ τ' h
  apply AlgHom.ext
  intro x
  exact ι.toRingHom.injective (congrArg (fun f : E →ₐ[Qp] LL' => f x) h)

theorem comp_bij {E : Type} [Field E] [Algebra Qp E] [FiniteDimensional Qp E] (ι : LL →ₐ[Qp] LL')
    (hcard : Nat.card (E →ₐ[Qp] LL) = finrank Qp E) :
    Function.Bijective (fun τ : E →ₐ[Qp] LL => ι.comp τ) :=
  (comp_inj ι).bijective_of_nat_card_le (hcard ▸ card_algHom_le_finrank Qp E LL')

variable [Fintype (K →ₐ[Qp] LL)] [Fintype (K →ₐ[Qp] LL')]

theorem thmELiftAt_bc (ι : LL →ₐ[Qp] LL') (v' : AddValuation LL' (WithTop ℚ))
    (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hfin : FiniteDimensional Qp LL') (hv' : v' (PD.p : LL') = 1)
    (hO' : ∃ hO : IsDomain O', @IsDiscreteValuationRing O' _ hO ∧ IsFractionRing O' LL')
    (hBC : BCAt PD (LL := LL) (O := O) (O' := O') ι)
    (H : ThmELiftAt PD (O := O') n (fun i => ι.comp (emb i)) v') :
    ThmELiftAt PD (O := O) n emb v := by
  intro hL h5 T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hK hJ hg hS hC hT hb1 hb2
    hW
  obtain ⟨T₁', T₂', F', hc₁', hc₂', hon', hj, -, hlift, -⟩ := hBC T₁ T₂ F hc₁ hc₂ hon
  apply hlift
  have := PD.finK
  have := PD.finK₀
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hL
  have hbK := comp_bij (E := K) ι (by rw [Nat.card_eq_fintype_card]; exact hG.1.2)
  have hbK₀ := comp_bij (E := K₀) ι (by
    rw [← Nat.card_congr (Equiv.ofBijective emb l4), Nat.card_zmod, l3])
  have hL' : Letters PD LL' v' (fun i => ι.comp (emb i)) :=
    ⟨l1, hfin, l3, hbK₀.comp l4, fun i => by
      change (ι.comp (emb (i + 1))).comp PD.σ = ι.comp (emb i)
      rw [AlgHom.comp_assoc, l5], hv'⟩
  have hG' : GoodCoeffs (K := K) (Qp := Qp) (LL := LL') (O := O') (V := T₁'.V) := by
    refine ⟨⟨hfin, ?_⟩, hc₁'.2.1, hO'⟩
    rw [← hG.1.2]
    exact (Fintype.card_of_bijective hbK).symm
  have tr₁ : ∀ (i : ZMod n) (X : Set ℤ), JumpsAtE PD T₁ emb i X →
      JumpsAtE PD T₁' (fun i => ι.comp (emb i)) i X := by
    intro i X hX τ' hτ' a ha
    obtain ⟨τ, rfl⟩ := hbK.2 τ'
    exact hX τ (comp_inj ι (by simpa [AlgHom.comp_assoc] using hτ')) a ((hj τ a).1.1 ha)
  have tr₂ : ∀ (i : ZMod n) (X : Set ℤ), JumpsAtE PD T₂ emb i X →
      JumpsAtE PD T₂' (fun i => ι.comp (emb i)) i X := by
    intro i X hX τ' hτ' a ha
    obtain ⟨τ, rfl⟩ := hbK.2 τ'
    exact hX τ (comp_inj ι (by simpa [AlgHom.comp_assoc] using hτ')) a ((hj τ a).2.1 ha)
  refine H hL' h5 T₁' T₂' F' hG' hc₁' hc₂' hon' j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂
    (fun i => tr₁ i _ (hK i)) ?_ hg hS hC hT (fun i => tr₁ i _ (hb1 i)) (fun i => tr₂ i _ (hb2 i)) hW
  intro τ' a ha
  obtain ⟨τ, rfl⟩ := hbK.2 τ'
  exact hJ τ a ((hj τ a).1.1 ha)

end Formalism.MainNotions.WachCoordinates.Br
end
end
