module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle369
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle217
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle365
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle364
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

theorem _root_.GlobalTheory.T.twistedFamily_potentiallyCrystalline_frobStable : ∀ (D : D7), PcrisTensorL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig0 : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ)) (c : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ) (n : ℕ),
  c ∈ Sig0 → Sig0.card ≤ n →
  (∀ x ∈ Xs, Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))) →
  (∀ x ∈ Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) Sig0) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) {c} →
  PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n := by
  first | exact @GlobalTheory.PotTwist.main | exact GlobalTheory.PotTwist.main | (intros; apply GlobalTheory.PotTwist.main <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.Pass.CutEq

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem main : ∀ (D : D7) (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i),
    PairedCharacterCondition.CongruenceModules.vccCut i Xs π = GlobalTheory.Cut.vccOff i Xs π := by
  intro D i Xs π
  have h : ccAt (D.nd.T i) (cutLocus i Xs) π = GlobalTheory.Cut.ccOff i Xs π := by
    unfold ccAt GlobalTheory.Cut.ccOff Ideal.map
    congr 1
    ext a
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨f.1, f.2, fun x hx hZ => ?_, rfl⟩
      have := congrFun (RingHom.mem_ker.1 hf) ⟨x, by simp [cutLocus, hx, hZ]⟩
      exact this
    · rintro ⟨f, hf, h0, rfl⟩
      refine ⟨⟨f, hf⟩, RingHom.mem_ker.2 (funext fun y => ?_), rfl⟩
      have hy := y.2
      simp only [cutLocus, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hy
      exact h0 y.1 hy.2 hy.1
  unfold vccCut GlobalTheory.Cut.vccOff
  rw [h]

end GlobalTheory.Pass.CutEq
end
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_quotientExtension_iff_admissible_ext : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ),
    (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) →
    ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T.ρ) (X : Type) [AddCommGroup X] [Module S.O X]
      (z : S.G → ↥L.T ⊗[S.O] X) (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤) (a : ℕ)
      (ha : ∀ x : X, S.Γ.lam ^ a • x = 0),
      (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
                         (tableLineDegreeTwo.kerExt L X S.Γ.lam a) ↔ S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩)) := by
  first | exact @GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' | exact GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' | (intros; apply GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm : ∀ (g : ℕ) [Fact g.Prime] (a b c n : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (γ : Gn g c → ℂ), IsClass α → IsClass β → IsClass γ → (n = a + b + c → hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n) ∧ (n = a + b → hc a b α β n = hc b a β α n) ∧ (hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α) := by
  first | exact @GlobalTheory.GLq.HcRing.main | exact GlobalTheory.GLq.HcRing.main | (intros; apply GlobalTheory.GLq.HcRing.main <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.mackey_formula_harishChandra_restriction_induction : ∀ (g : ℕ) [Fact g.Prime] (a b c d n : ℕ), n = a + b → n = c + d → ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) → ∀ h₁ h₂, res c d (hcT a b Φ n) h₁ h₂ = ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b), hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁ := by
  first | exact @GlobalTheory.GLq.Mackey.mackey_formula | exact GlobalTheory.GLq.Mackey.mackey_formula | (intros; apply GlobalTheory.GLq.Mackey.mackey_formula <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.whittakerDimension_harishChandraInduction_mul : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (a b n : ℕ), n = a + b → ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) → wh ψ (hcT a b Φ n) = wh ψ (fun x => wh ψ (Φ x)) := by
  first | exact @GlobalTheory.GLq.WhMul.wh_hcT | exact GlobalTheory.GLq.WhMul.wh_hcT | (intros; apply GlobalTheory.GLq.WhMul.wh_hcT <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.character_decomposition_and_classFunction_expansion : ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsChar χ → ∃ L : List (G → ℂ), (∀ ρ ∈ L, IsIrr ρ) ∧ χ = L.sum) ∧ (IsClass χ → χ = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, ip χ ρ • ρ) ∧ (IsChar χ → IsClass χ) ∧ (IsChar χ → ip χ χ = 1 → IsIrr χ) ∧ (∀ L : List (G → ℂ), (∀ ρ ∈ L, IsChar ρ) → IsChar L.sum) := by
  first | exact @GlobalTheory.charDec | exact GlobalTheory.charDec | (intros; apply GlobalTheory.charDec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem unr_of_iterate_fixed :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h →
      ∀ c : P.R.B, P.φB^[h] c = c → (∀ j < h, ev P j c ∈ Fil P 0) →
        ∃ a : ↥(MaximalUnramifiedExtension l), fr l h a = a ∧ c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a := by
  intro l _ P AI T h hh c hc hF
  obtain ⟨E, ω, hEle, hEdim, hEfix, -⟩ := GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l h hh
  have hK0 : K0 E = E.1 := inf_eq_left.2 hEle
  have hdim : Module.finrank ℚ_[l] ↥(K0 E) = h := by rw [hK0]; exact hEdim
  have hper : Function.IsPeriodicPt (⇑P.φB) h c := hc
  have hall : ∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD E).Fil 0 := by
    intro j
    have hj : (⇑P.φB)^[j] c = (⇑P.φB)^[j % h] c := by
      conv_lhs => rw [← Nat.mod_add_div j h]
      rw [Function.iterate_add_apply, (hper.mul_const (j / h)).eq]
    have h1 := hF (j % h) (Nat.mod_lt _ hh)
    rw [← SetLike.mem_coe, ← P.PD_Fil _ E 0, hj]
    exact h1
  obtain ⟨a, ha⟩ := GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt l P AI T E c (by rw [hdim]; exact hc) hall
  refine ⟨⟨(a : Om l), a.2.2⟩, ?_, ?_⟩
  · exact (hEfix ⟨(a : Om l), a.2.2⟩).2 a.2.1
  · rw [ha]; rfl

end GlobalTheory.PMon
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.exists_continuous_coords_unramified_frobenius : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) ∧ (∀ k, fr l r (ω k) = ω k) ∧
    ∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k) := by
  first | exact @GlobalTheory.PMon.coef_unr_continuous | exact GlobalTheory.PMon.coef_unr_continuous | (intros; apply GlobalTheory.PMon.coef_unr_continuous <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

theorem _root_.GlobalTheory.T.concreteProjector_eq_orthogonalProjection : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → Function.Injective ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) = LinearMap.range ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ∀ x, eMt i t x - ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ((lPrj D A P ψ Zs i t).mulVec x) ∈ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ := by
  first | exact @GlobalTheory.EtaJoin.concreteProj_orth | exact GlobalTheory.EtaJoin.concreteProj_orth | (intros; apply GlobalTheory.EtaJoin.concreteProj_orth <;> assumption)
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense : ∀ (D : D7), GlobalTheory.TypeLeaf.FrobDense D → ∀ (i : D.ntw.Tw) (s : D.ntw.Sig i), FrobDual i s → CharDual i s := by
  first | exact @GlobalTheory.CharDualDense.charDual_of_frobDual | exact GlobalTheory.CharDualDense.charDual_of_frobDual | (intros; apply GlobalTheory.CharDualDense.charDual_of_frobDual <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem RestrScalars.fr_smul (l : ℕ) [Fact l.Prime] (m : ℕ) (a : ℚ_[l]) (x : ↥(MaximalUnramifiedExtension l)) : fr l m (a • x) = a • fr l m x := by
  show (frobUr l ^ m) (a • x) = a • (frobUr l ^ m) x
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]

theorem RestrScalars.fr_comm_pow (l : ℕ) [Fact l.Prime] (a b : ℕ) (x : ↥(MaximalUnramifiedExtension l)) : fr l a (fr l b x) = fr l b (fr l a x) := by
  show (frobUr l ^ a) ((frobUr l ^ b) x) = (frobUr l ^ b) ((frobUr l ^ a) x)
  rw [← AlgHom.mul_apply, ← AlgHom.mul_apply, ← pow_add, ← pow_add, add_comm]

theorem weilRes_of_basis (hE : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (E : FinExt l) (ω : Fin r → ↥(MaximalUnramifiedExtension l)),
      E.1 ≤ MaximalUnramifiedExtension l ∧ Module.finrank ℚ_[l] ↥E.1 = r ∧ (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ↔ (c : Om l) ∈ E.1) ∧
      (∀ k, fr l r (ω k) = ω k) ∧ LinearIndependent ℚ_[l] ω ∧
      (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) ∧
      (Matrix.of fun m k : Fin r => fr l m (ω k)).det ≠ 0) : WeilRes := by
  intro l _ n _ _ K r ρ hρ
  obtain ⟨E, ω, -, -, -, hωf, hli, hsp, hdet⟩ := hE l r hρ.pos

  set v : Fin r → Om l := fun k => ((ω k : ↥(MaximalUnramifiedExtension l)) : Om l) with hvdef
  have hv : LinearIndependent ℚ_[l] v := by
    have := hli.map' ((MaximalUnramifiedExtension l).val.toLinearMap) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    exact this
  set S : Submodule ℚ_[l] (Om l) := Submodule.span ℚ_[l] (Set.range v)
  let bS : Module.Basis (Fin r) ℚ_[l] S := Module.Basis.span hv
  haveI : FiniteDimensional ℚ_[l] S := Module.Finite.of_basis bS
  have coe_sum : ∀ a : Fin r → ℚ_[l], (((∑ k, a k • ω k : ↥(MaximalUnramifiedExtension l))) : Om l) = ∑ k, a k • v k := by
    intro a
    simp [hvdef]
  have memS : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ S := by
    intro c hc
    obtain ⟨a, rfl⟩ := hsp c hc
    rw [coe_sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have fix : ∀ g i j k, fr l r ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k := by
    intro g i j k
    rw [map_mul, hρ.rat, hωf]

  let co : ↥(GK K) → n → n → Fin r → Fin r → ℚ_[l] := fun g i j k k' =>
    bS.repr ⟨_, memS _ (fix g i j k)⟩ k'
  have hco : ∀ g i j k, ∑ k', co g i j k k' • ω k' = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k := by
    intro g i j k
    apply Subtype.val_injective
    rw [coe_sum]
    have h := bS.sum_repr ⟨_, memS _ (fix g i j k)⟩
    have h2 := congrArg Subtype.val h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Module.Basis.span_apply]
  let M : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ℚ_[l] := fun g =>
    Matrix.of fun x y => co g x.1 y.1 y.2 x.2

  let W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l) := Matrix.of fun m k : Fin r => fr l m (ω k)
  let pm : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := Matrix.kroneckerMap (· * ·) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) W
  have hpdet : pm.det ≠ 0 := by
    have : pm.det = W.det ^ Fintype.card n := by
      exact (Matrix.det_kronecker (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) W).trans (by simp)
    rw [this]
    exact pow_ne_zero _ hdet
  let pU : GL (n × Fin r) ↥(MaximalUnramifiedExtension l) := ((Matrix.isUnit_iff_isUnit_det pm).mpr (isUnit_iff_ne_zero.mpr hpdet)).unit
  have hpU : (pU : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = pm := rfl
  let D : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := fun g =>
    Matrix.blockDiagonal (fun m : Fin r => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))
  have key : ∀ g, pm * (M g).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = D g * pm := by
    intro g
    refine Matrix.ext fun x y => ?_
    obtain ⟨i, m⟩ := x
    obtain ⟨j, k⟩ := y
    simp only [pm, D, M, W, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_ite_irrel, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.blockDiagonal_apply, Matrix.map_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]

    rw [← map_mul, ← hco g i j k, map_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [RestrScalars.fr_smul, Algebra.smul_def, mul_comm]
  have key' : ∀ g, (M g).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = ((pU⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix _ _ _) * D g * pm := by
    intro g
    rw [Matrix.mul_assoc, ← key g, ← Matrix.mul_assoc, ← hpU, Units.inv_mul, Matrix.one_mul]
  have hinj : Function.Injective (fun X : Matrix (n × Fin r) (n × Fin r) ℚ_[l] => X.map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) :=
    Matrix.map_injective (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).injective
  have Dmul : ∀ g h, D (g * h) = D g * D h := by
    intro g h
    simp only [D]
    rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext m
    rw [map_mul, Units.val_mul]
    exact Matrix.map_mul
  have D1 : D 1 = 1 := by
    simp only [D, map_one, Units.val_one]
    rw [← Matrix.blockDiagonal_one]
    congr 1
    funext m
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let f : ↥(GK K) →* Matrix (n × Fin r) (n × Fin r) ℚ_[l] :=
    { toFun := M
      map_one' := by
        apply hinj
        simp only
        rw [key', D1, Matrix.mul_one, ← hpU, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      map_mul' := by
        intro g h
        apply hinj
        simp only
        rw [Matrix.map_mul, key', key', key', Dmul]
        have : pm * ((pU⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix _ _ _) = 1 := by rw [← hpU, Units.mul_inv]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc pm, this, Matrix.one_mul] }
  refine ⟨f.toHomUnits, pU, ?_, ?_, ?_⟩
  · intro x y
    have hc : Continuous fun g : ↥(GK K) => bS.coord x.2 ⟨_, memS _ (fix g x.1 y.1 y.2)⟩ := by
      refine (LinearMap.continuous_of_finiteDimensional (bS.coord x.2)).comp ?_
      refine Continuous.subtype_mk ?_ _
      exact (hρ.cont x.1 y.1).mul continuous_const
    simpa [f, M, co] using hc
  · intro x y
    rw [hpU]
    obtain ⟨i, m⟩ := x
    obtain ⟨j, k⟩ := y
    simp only [pm, W, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    split_ifs
    · rw [RestrScalars.fr_comm_pow, hωf]
    · exact map_zero _
  · intro g
    rw [hpU]
    exact key g

theorem weilRes : WeilRes := weilRes_of_basis GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree

end GlobalTheory.PMon

end
end
