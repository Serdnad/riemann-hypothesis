module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle328
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Mathlib.Topology.Algebra.Group.Units
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle330
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle329
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle327
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle331
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.frobenius_reciprocity_nonzero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V) (hτ : IsSmooth τ) (f : (jac (stdBlocks (fun a => (x a).1) hd) τ).IntertwiningMap (piTensor fun a => (x a).rep)) (hf : ∃ v, f v ≠ 0), ∃ g : τ.IntertwiningMap (prodIrr x hd), ∃ v, g v ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr | exact GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr | (intros; apply GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.cosocle_surjection_factor : ∀ {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V) (Q : Representation ℂ G X) (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (f : P.IntertwiningMap Q) (hf : Function.Surjective f) (hQ : Nontrivial X), ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  first | exact @GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient | exact GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient | (intros; apply GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.bijective_intertwiner_subrep_equiv : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W) (S : Subrepresentation ρ) (O : S.toSubmodule →ₗ[ℂ] W), Function.Bijective O → (∀ (g : G) (v : S.toSubmodule), O ⟨ρ g v, S.apply_mem_toSubmodule g v.2⟩ = τ g (O v)) → Nonempty ((subQuot S ⊥).Equiv τ) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective | exact GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective | (intros; apply GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.surjective_intertwiner_quotient_equiv : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W) (R : ρ.IntertwiningMap τ), Function.Surjective R → ∃ S : Subrepresentation ρ, S.toSubmodule = LinearMap.ker R.toLinearMap ∧ Nonempty ((subQuot ⊤ S).Equiv τ) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv | exact GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv | (intros; apply GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.cuspidal_twist_injective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hx : x.IsCusp) (a b : ℕ) (h : x.nu (a : ℂ) = x.nu (b : ℂ)), a = b := by
  first | exact @GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | exact GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | (intros; apply GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.segment_term_injective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), Function.Injective Δ.term := by
  first | exact @GlobalTheory.CompanionTheory.SegTerm.term_injective | exact GlobalTheory.CompanionTheory.SegTerm.term_injective | (intros; apply GlobalTheory.CompanionTheory.SegTerm.term_injective <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

theorem _root_.GlobalTheory.T.cosocle_of_contragredient_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ τ' : IrrRep (GL (Fin N) k), IsSocle τ'.ρ (contra π) → ∃ τ : IrrRep (GL (Fin N) k), IsCosocle τ.ρ π := by
  first | exact @GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra | exact GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra | (intros; apply GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.cosocle_contragredient_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → IsCosocle σ π → IsSocle (contra σ) (contra π) := by
  first | exact @GlobalTheory.CompanionTheory.SocleContra.isSocle_contra_of_isCosocle | exact GlobalTheory.CompanionTheory.SocleContra.isSocle_contra_of_isCosocle | (intros; apply GlobalTheory.CompanionTheory.SocleContra.isSocle_contra_of_isCosocle <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd.ProdDrop

section Blocks

variable (k : Type) [Field k] {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r)
  (ho : StrictMono o) (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (hd' : ∑ a, d (o a) = N)

include ho hz

theorem mem_parab_drop (g : GL (Fin N) k) :
    g ∈ parab k (stdBlocks d hd) ↔ g ∈ parab k (stdBlocks (fun a => d (o a)) hd') := by
  have hE := GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty d hd o ho hz hd'
  rw [mem_parab_iff, mem_parab_iff]
  constructor
  · intro h a b i j hab
    rw [hE, hE]
    exact h _ _ i j (ho hab)
  · intro h a b i j hab
    obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
    obtain ⟨b, rfl⟩ := hz b (Nat.pos_iff_ne_zero.1 (Fin.pos j))
    have := h a b i j (ho.lt_iff_lt.1 hab)
    rwa [hE, hE] at this

theorem dropHom_leviProj (p : parab k (stdBlocks d hd)) (q : parab k (stdBlocks (fun a => d (o a)) hd'))
    (h : (p : GL (Fin N) k) = q) :
    dropHom d o (leviProj k (stdBlocks d hd) p) = leviProj k (stdBlocks (fun a => d (o a)) hd') q := by
  have hE := GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty d hd o ho hz hd'
  funext a
  ext i j
  show (leviProj k (stdBlocks d hd) p (o a) : Matrix _ _ k) i j = _
  rw [leviProj_apply, leviProj_apply, hE, hE, h]

theorem modExp_drop (a : Fin r') :
    modExp (fun j => Fin (d j)) (o a) = modExp (fun b => Fin (d (o b))) a := by
  have h0 : ∀ j, j ∉ Set.range o → d j = 0 := fun j hj => by_contra fun h => hj (hz j h)
  unfold modExp
  simp only [Fintype.card_fin, Finset.sum_filter]
  congr 1
  · refine (Fintype.sum_of_injective o ho.injective _ _ (fun j hj => ?_) fun b => ?_).symm
    · simp [h0 j hj]
    · simp [ho.lt_iff_lt]
  · refine (Fintype.sum_of_injective o ho.injective _ _ (fun j hj => ?_) fun b => ?_).symm
    · simp [h0 j hj]
    · simp [ho.lt_iff_lt]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r)
  (ho : StrictMono o) (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (hd' : ∑ a, d (o a) = N)


include ho hz in
theorem deltaHalf_drop (g : Levi k fun j => Fin (d j)) :
    deltaHalf k (fun j => Fin (d j)) g = deltaHalf k (fun a => Fin (d (o a))) (dropHom d o g) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine (Fintype.prod_of_injective o ho.injective _ _ (fun j hj => ?_) fun a => ?_).symm
  · have hj0 : d j = 0 := by_contra fun h => hj (hz j h)
    have : IsEmpty (Fin (d j)) := by rw [hj0]; infer_instance
    have h1 : Matrix.GeneralLinearGroup.det (g j) = 1 := Units.ext (by simp [Matrix.det_isEmpty])
    rw [h1, map_one]
  · rw [modExp_drop d o ho hz]
    rfl


include ho hz in
theorem parInd_comp_dropHom_equiv {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun a => Fin (d (o a))) W) :
    Nonempty ((parInd (stdBlocks d hd) (τ.comp (dropHom d o) : Representation ℂ (Levi k fun j => Fin (d j)) W)).Equiv
      (parInd (stdBlocks (fun a => d (o a)) hd') τ)) := by
  have key : ∀ (p : parab k (stdBlocks d hd)) (q : parab k (stdBlocks (fun a => d (o a)) hd')),
      (p : GL (Fin N) k) = q →
      _root_.GlobalTheory.SmGL.twist (τ.comp (dropHom d o) : Representation ℂ (Levi k fun j => Fin (d j)) W) (deltaHalf k _)
          (leviProj k (stdBlocks d hd) p) =
        _root_.GlobalTheory.SmGL.twist τ (deltaHalf k _) (leviProj k (stdBlocks (fun a => d (o a)) hd') q) := fun p q h => by
    refine LinearMap.ext fun v => ?_
    rw [_root_.GlobalTheory.SmGL.twist_apply, _root_.GlobalTheory.SmGL.twist_apply, deltaHalf_drop d o ho hz, dropHom_leviProj k d hd o ho hz hd' p q h]
    show _ • τ (dropHom d o _) v = _
    rw [dropHom_leviProj k d hd o ho hz hd' p q h]
  refine Placing.smInd_equiv 1
    (fun q => ⟨⟨q.1, (mem_parab_drop k d hd o ho hz hd' q.1).2 q.2⟩, by simp, key _ _ rfl⟩)
    (fun p => ⟨⟨p.1, (mem_parab_drop k d hd o ho hz hd' p.1).1 p.2⟩, by simp, (key _ _ rfl).symm⟩)

end Local



theorem prodIrr_drop : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr (fun a => y (o a)) hd')) := by
  intro k _ _ _ _ r r' N y hd o ho hz hd'
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv y o ho hz
  obtain ⟨χ⟩ := parInd_comp_dropHom_equiv (k := k) (fun j => (y j).1) hd o ho hz hd'
    (piTensor fun a => (y (o a)).rep)
  have e1 := parIndEquiv (stdBlocks (fun j => (y j).1) hd) φ
  have e2 := e1.trans χ
  unfold prodIrr multiProd
  exact ⟨e2⟩

end GlobalTheory.CompanionTheory.FineProd.ProdDrop

end
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.torsion_norm_zeta_bound : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ r : ℝ, 1 < r → Summable (fun x : (Fin m → K) ⧸ L => (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' x : (Fin m → K) ⧸ L, (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r)) ≤ zetaR K r := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.congruence_subgroups_basis_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (O : Set (Mir k n)) (hO : O ∈ nhds (1 : Mir k n)),
  ∃ s₀ : kˣ, ∀ (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1), ValuativeRel.valuation k (s : k) ≤ ValuativeRel.valuation k (s₀ : k) →
    (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ⊆ O := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM_subset_nhds | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM_subset_nhds | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM_subset_nhds <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.congruence_subgroup_open_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1),
  IsOpen (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ∧ IsCompact (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM_isOpen_isCompact | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM_isOpen_isCompact <;> assumption)
end
