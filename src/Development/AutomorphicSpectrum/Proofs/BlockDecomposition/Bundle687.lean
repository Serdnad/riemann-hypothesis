module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalIdeleHermitianBound
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle683
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle343
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle654
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle681
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle641
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingIdentityOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle676
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle682
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.levi_minimal_idele_hermitian_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ m ∈ leviMin σ J X Y, m ∈ minParOne σ J X → ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (hermFam σ J X Y j) ((matHom _ σ J m⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J m⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (hermFam σ J X Y j) ξ ξ) := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.hermFam_levi_scale | exact GlobalTheory.CompanionTheory.ParCocompact.hermFam_levi_scale | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.hermFam_levi_scale <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.mem_levi_minimal_of_commutes_projections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) = (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ leviMin σ J X Y ∧ γ ∈ minParOne σ J X := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm | exact GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.square_integrable_single_segment : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one | exact GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one | (intros; apply GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegFineCons

theorem finSigmaFinEquiv_one_val {s : ℕ} (i : Fin s) (b : Fin 1) :
    ((finSigmaFinEquiv (m := s) (n := fun _ => 1) ⟨i, b⟩ : Fin _) : ℕ) = i := by
  rw [finSigmaFinEquiv_apply, Subsingleton.elim b 0]
  simp

theorem eq_one_of_sum_eq {s : ℕ} (c : Fin s → ℕ) (h1 : ∀ a, 1 ≤ c a) (h : ∑ a, c a = s) (a : Fin s) : c a = 1 := by
  have h2 : ∑ _a : Fin s, 1 = ∑ a, c a := by simpa using h.symm
  exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => h1 i)).1 h2 a (Finset.mem_univ a)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem sum_concat_fst {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ b, (x a b).1 := by
  rw [← Fintype.sum_sigma' (fun a b => (x a b).1)]
  exact Equiv.sum_comp finSigmaFinEquiv.symm (fun p : Σ a, Fin (c a) => (x p.1 p.2).1)


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem concat_finSigmaFinEquiv {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (p : Σ a, Fin (c a)) :
    concat c x (finSigmaFinEquiv p) = x p.1 p.2 := by
  have key : ∀ q : Σ a, Fin (c a), q = p → x q.1 q.2 = x p.1 p.2 := by
    rintro _ rfl
    rfl
  exact key _ (Equiv.symm_apply_apply _ _)

theorem exists_cusp_word (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (y : IrrGL (k := k)) :
    ∃ (c : ℕ) (x : Fin c → IrrGL (k := k)) (hd : ∑ b, (x b).1 = y.1), (∀ b, (x b).IsCusp) ∧ 1 ≤ jm x hd y.rep := by
  obtain ⟨c, x, hd, hc, φ, hφ⟩ := GlobalTheory.CompanionTheory.SubEmb.subEmbedding k y.1 _ y.rep y.2.rep.smooth y.2.rep.irr
  have := Model.nontrivial_of_isIrreducible y.2.rep.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.2.rep.V)
  exact ⟨c, x, hd, hc, GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA x hd _ y.2.rep.smooth φ
    ⟨v, fun h => hv (hφ (h.trans (map_zero φ).symm))⟩⟩

theorem equiv_piTensor_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJac Γ) (u : IrrGL (k := k)) (hu : IsLSeg Γ u.rep) (hs : ∑ i, (dec Γ i).1 = u.1) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Levi k fun i => Fin ((dec Γ i).1)) X), ρ.IsIrreducible → IsSubquotient ρ (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep) → Nonempty (ρ.Equiv (piTensor fun i => (dec Γ i).rep)) := by
  intro k _ _ _ _ hA Γ hF u hu hs X _ _ ρ hi hsub
  have hsm : IsSmooth ρ := hsub.isSmooth (isSmooth_jac _ u.2.rep.smooth)
  obtain ⟨σ, ⟨E⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (fun i => (dec Γ i).1) (⟨X, ρ, hsm, hi⟩ : IrrRep _)
  replace E : ρ.Equiv (piTensor fun a => (σ a).rep.ρ) := E
  suffices hσ : σ = fun a => (dec Γ a).2 by
    subst hσ
    exact ⟨E⟩
  let y : Fin Γ.len → IrrGL (k := k) := fun i => ⟨(dec Γ i).1, σ i⟩
  have hy : ∑ a, (y a).1 = u.1 := hs
  have h1 : 1 ≤ jm y hy u.rep := Order.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2
    ((IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective).trans hsub))
  choose c x hd hcusp hpos using fun a => exists_cusp_word hA (y a)
  have hcat : ∑ i, (concat c x i).1 = u.1 := by
    rw [sum_concat_fst, ← hy]
    exact Finset.sum_congr rfl fun a _ => hd a
  have h2 : 1 ≤ jm (concat c x) hcat u.rep := h1.trans
    (GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat hA y hy c x hd hcat hpos u.rep u.2.rep.smooth
      (hasFiniteLength_of_isIrreducible u.2.rep.irr))
  obtain ⟨h, hcon⟩ := (hF u.rep hu).2 _ (concat c x) hcat (fun a => hcusp _ _) h2
  have hc0 : ∀ a, 1 ≤ c a := fun a => by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; exact Fin.isEmpty
    have h3 : (y a).1 = 0 := by rw [← hd a]; simp
    exact Γ.d_pos.ne' h3
  obtain rfl : c = fun _ => 1 := funext (eq_one_of_sum_eq c hc0 h)
  funext a
  have h3 : x a 0 = dec Γ (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) :=
    (concat_finSigmaFinEquiv _ x ⟨a, 0⟩).symm.trans (hcon (finSigmaFinEquiv ⟨a, 0⟩))
  have h4 : dec Γ (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) = dec Γ a :=
    congrArg _ (Fin.ext (finSigmaFinEquiv_one_val a 0))
  have h5 : x a 0 = y a := GlobalTheory.CompanionTheory.SegFine.eq_of_one_le_jm (y a) (y a).rep (.refl _) (x a) (hd a) (hpos a)
  have h6 : (⟨(dec Γ a).1, σ a⟩ : IrrGL (k := k)) = ⟨(dec Γ a).1, (dec Γ a).2⟩ := (h5.symm.trans h3).trans h4
  exact sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h6

end GlobalTheory.CompanionTheory.SegFineCons

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.langlands_socle_of_order_free : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k → LOrderFree k → LSocleGL k := by
  first | exact @GlobalTheory.CompanionTheory.LSocle.lSocleGL | exact GlobalTheory.CompanionTheory.LSocle.lSocleGL | (intros; apply GlobalTheory.CompanionTheory.LSocle.lSocleGL <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcB.F.MLM (muAt MOk MatchLMB2)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchLMB2

section Scale

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Scale

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mconv_left {a b : ℕ} {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} {f : LF a b w} (g : LF a b w)
    (hf : ∀ u ∈ U, ∀ x, f (u * x) = f x) {u : GLw a w × GLw b w} (hu : u ∈ U) (m : GLw a w × GLw b w) :
    mconv f g (u * m) = mconv f g m := by
  unfold mconv
  rw [← GlobalTheory.CompanionTheory.CtMulSplit.hint_left _ u]
  congr 1
  funext z
  rw [hf u hu z]
  congr 2
  group

theorem tr_one (d : LocData E n) {a : ℕ} (L : LM d.kap a (n - a)) {w : Pl E} (hw : w ∈ d.P) :
    L.tr d.P d.one w = ∑ x, L.m w x x := by
  unfold LM.tr
  rw [if_pos hw]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · simp [LocData.one]
  · intro y _ hy
    simp [LocData.one, hy]
  · simp

theorem sum_kap_alt (d : LocData E n) {w : Pl E} (hT : w ∈ d.T) {M : Type} [AddCommMonoid M]
    (F : Finset (Fin (n / 2)) → M) : ∑ x : d.kap w, F x.1.1 = ∑ s, F s := by
  have e : d.idx w = Finset.univ ×ˢ {1} := by
    unfold LocData.idx
    rw [if_pos hT]
  rw [Finset.sum_coe_sort (d.idx w) (fun p => F p.1), e, Finset.sum_product]
  simp

end Alg

section TPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem qT_mpow_left (d : LocData E n) {a : ℕ} (w : Pl E) (s : Finset (Fin (n / 2))) (k : ℕ)
    {u : GLw a w × GLw (n - a) w} (hu : u ∈ I2 a (n - a) w) (g : GLw a w × GLw (n - a) w) :
    MT.mpow w (d.qT a w s) (k + 1) (u * g) = MT.mpow w (d.qT a w s) (k + 1) g :=
  mconv_left _ (fun _ hv t => (GlobalTheory.CompanionTheory.MatchId.qT_inv d s hv t).1) hu g

theorem powers_diagonal_at_T_block (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hT : w ∈ d.T) (k : ℕ) (x y : d.kap w) :
    (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) k).m w x y = d.diag (fun x => MT.mpow w (d.qT a w x.1.1) (k + 1)) x y := by
  have hb : ∀ x y : d.kap w, (d.betaL a ha).m w x y = d.diag (fun x => d.qT a w x.1.1) x y := fun x y => by
    show (if w ∈ d.T then _ else _) = _
    rw [if_pos hT]
  induction k generalizing x y with
  | zero =>
    show (d.betaL a ha).m w x y = _
    rw [hb]
    unfold LocData.diag
    split_ifs
    · exact (GlobalTheory.CompanionTheory.FmPowP.mconv_idem_right (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open a (n - a) w) (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_le_maximal a (n - a) w)
        (d.qT a w x.1.1) fun u hu g => (GlobalTheory.CompanionTheory.MatchId.qT_inv d _ hu g).2).symm
    · rfl
  | succ k ih =>
    show ∑ z, mconv ((d.betaL a ha).m w x z) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) k).m w z y) = _
    simp only [hb, ih]
    rw [GlobalTheory.CompanionTheory.MatchId.sum_mconv_diag_left d (fun z => d.diag (fun x => MT.mpow w (d.qT a w x.1.1) (k + 1)) z y)]
    unfold LocData.diag
    split_ifs with h
    · rfl
    · exact GlobalTheory.CompanionTheory.MatchId.mconv_zero_right _

theorem trace_test_function_eq (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hT : w ∈ d.T) (m : ℕ) :
    ((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).tr d.P d.one w =
      fun y => ∑ s, MT.mpow w (d.qT a w s) (m + 1) y := by
  have hP : w ∈ d.P := Finset.mem_union_left _ hT
  have hlev : d.lev a w = I2 a (n - a) w := by
    unfold LocData.lev
    rw [if_pos hT]
  have hent : ∀ x : d.kap w, ((d.fixL a).mul (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m)).m w x x =
      MT.mpow w (d.qT a w x.1.1) (m + 1) := by
    intro x
    show ∑ z, mconv ((d.fixL a).m w x z) ((PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w z x) = _
    have e : ∀ z, (d.fixL a).m w x z = d.diag (fun _ => PositivityTheory.Rg.BcB.F.idem (I2 a (n - a) w)) x z := fun z => by
      show d.diag (fun _ => if w ∈ d.T then PositivityTheory.Rg.BcB.F.idem (d.lev a w) else d.sgn a w • PositivityTheory.Rg.BcB.F.idem (d.lev a w)) x z = _
      rw [if_pos hT, hlev]
    simp only [e]
    rw [GlobalTheory.CompanionTheory.MatchId.sum_mconv_diag_left d (fun z => (PositivityTheory.Rg.BcB.F.MLM.pw (d.betaL a ha) m).m w z x), powers_diagonal_at_T_block d ha hT]
    unfold LocData.diag
    rw [if_pos rfl]
    exact GlobalTheory.CompanionTheory.FmPowP.mconv_idem_left (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open a (n - a) w) (GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_le_maximal a (n - a) w) _
      fun u hu g => qT_mpow_left d w _ m hu g
  rw [tr_one d _ hP]
  funext y
  rw [Finset.sum_apply]
  simp only [hent]
  exact sum_kap_alt d hT (fun s => MT.mpow w (d.qT a w s) (m + 1) y)

end TPlace

section SPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end SPlace

section BadPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end BadPlace

end GlobalTheory.CompanionTheory.MatchLMB2

end
end

section


theorem _root_.GlobalTheory.T.matching_identity_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMIdOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | exact GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | (intros; apply GlobalTheory.CompanionTheory.MatchId.matchLMIdOf <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcB.F.MLM (wordLS wordUS CtStar)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchWordS

open GlobalTheory.CompanionTheory.MatchWord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isHecke_lstar {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) : IsHecke (KL n w) (lstar f) := by
  refine ⟨(hf.1.comp_homeomorph (Homeomorph.inv _)).comp_left (map_zero (starRingEnd ℂ)), fun k hk x => ⟨?_, ?_⟩⟩
  · simp only [lstar, _root_.mul_inv_rev, (hf.2 _ (inv_mem hk) _).2]
  · simp only [lstar, _root_.mul_inv_rev, (hf.2 _ (inv_mem hk) _).1]

def letU (d : LocData E n) (w : Pl E) (x : ℕ × Bool × Bool) : UL n w → ℂ :=
  if x.2.2 then lstar (d.hU w x.1) else d.hU w x.1

def letL (d : LocData E n) (a : ℕ) (ha : a ≤ n) (w : Pl E) (x : ℕ × Bool × Bool) : LM d.kap a (n - a) :=
  if x.2.2 then (d.hL a ha w x.1 x.2.1).adj else d.hL a ha w x.1 x.2.1

theorem word_ct (d : LocData E n) (a : ℕ) (ha : a ≤ n) {w : Pl E} (hCt : MT.CtMul) (hSt : CtStar) (hSp : SphComm) (hE : Unr E)
    (hd : d.Ok) (hG : d.Good w) (hN : ∀ u, ‖((d.μ w u : ℂˣ) : ℂ)‖ = 1) (l : List (ℕ × Bool × Bool)) :
    IsHecke (KL n w) (wordUS d w l) ∧ ∃ A B : UL n w → ℂ, IsHecke (KL n w) A ∧ IsHecke (KL n w) B ∧
      (wordLS d a ha w l).s w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A ∧
      (wordLS d a ha w l).t w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B ∧
      mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A) (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B) =
        ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l) := by
  have hG' := hG
  obtain ⟨hw, hT, hS₀, hBad, hμ⟩ := hG
  have hU : UL n w = ⊤ := if_pos hw
  set C := ctMu (Nat.add_sub_cancel' ha) w (d.μ w) with hC
  have conv : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → IsHecke (KL n w) (lconv f g) :=
    fun hf hg => GlobalTheory.CompanionTheory.UnitaryWord.isHecke_lconv GlobalTheory.CompanionTheory.LocHecke.locAlg (GlobalTheory.CompanionTheory.MatchPowers.isLevel_KL n w) hf hg
  have mul : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → C (lconv f g) = mconv (C f) (C g) :=
    fun hf hg => hCt E n a ha w hw (d.μ w) hμ _ _ hf hg
  have star : ∀ {f : UL n w → ℂ}, IsHecke (KL n w) f → lfStar (C f) = C (lstar f) :=
    fun hf => (hSt E n a ha w hw (d.μ w) hN _ hf).symm
  have hone : IsHecke (KL n w) (lone (KL n w)) := GlobalTheory.CompanionTheory.MatchUnit.isHecke_lone_KL hE
  have hunit : C (lone (KL n w)) = PositivityTheory.Rg.BcB.F.idem (K2 a (n - a) w) := GlobalTheory.CompanionTheory.MatchUnit.ctMu_lone _ hU _ hμ
  have hlev : d.lev a w = K2 a (n - a) w := by
    unfold LocData.lev
    rw [if_neg hT, if_neg (by simp [hS₀, hBad])]
  have hlev₂ : d.lev₂ a w = K2 a (n - a) w := by
    unfold LocData.lev₂
    rw [if_neg (by simp [hS₀, hBad])]
  have hes : (d.eL a).s w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev a w) = _
    rw [hlev]
  have het : (d.eL a).t w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev₂ a w) = _
    rw [hlev₂]
  have hstar1 : lfStar (C (lone (KL n w))) = C (lone (KL n w)) := by
    rw [hunit, PositivityTheory.Rg.BcB.F.LocComm.lfStar_idem]
  have hH : ∀ x, IsHecke (KL n w) (letU d w x) := by
    rintro ⟨k, intersection_update_fsHerm_neg_one, st⟩
    have hTk := isHecke_hU d hd hU k
    cases st
    · exact hTk
    · exact isHecke_lstar hTk
  have hck : ∀ k, d.hc a ha w k = C (d.hU w k) := fun k => hc_eq d a ha hμ k
  have hl0 : ∀ k st, (letL d a ha w (k, false, st)).s w = C (letU d w (k, false, st)) ∧
      (letL d a ha w (k, false, st)).t w = C (lone (KL n w)) := by
    intro k st
    have e : (d.hL a ha w k false).s w = d.hc a ha w k := by simp [LocData.hL]
    cases st
    · exact ⟨by simpa [letL, letU] using e.trans (hck k), het⟩
    · refine ⟨?_, ?_⟩
      · show lfStar ((d.hL a ha w k false).s w) = C (lstar (d.hU w k))
        rw [e, hck, star (isHecke_hU d hd hU k)]
      · show lfStar ((d.eL a).t w) = _
        rw [het, hstar1]
  have hl1 : ∀ k st, (letL d a ha w (k, true, st)).s w = C (lone (KL n w)) ∧
      (letL d a ha w (k, true, st)).t w = C (letU d w (k, true, st)) := by
    intro k st
    have e : (d.hL a ha w k true).t w = d.hc a ha w k := by simp [LocData.hL]
    cases st
    · exact ⟨hes, by simpa [letL, letU] using e.trans (hck k)⟩
    · refine ⟨?_, ?_⟩
      · show lfStar ((d.eL a).s w) = _
        rw [hes, hstar1]
      · show lfStar ((d.hL a ha w k true).t w) = C (lstar (d.hU w k))
        rw [e, hck, star (isHecke_hU d hd hU k)]
  induction l with
  | nil =>
    refine ⟨?_, lone (KL n w), lone (KL n w), hone, hone, hes, het, ?_⟩
    · show IsHecke (KL n w) ((KL n w : Set (UL n w)).indicator 1)
      rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL] at hone
      exact hone
    · rw [← mul hone hone, lconv_lone_left hone, GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
      rfl
  | cons x l ih =>
    obtain ⟨hW, A, B, hA, hB, hs, ht, hm⟩ := ih
    obtain ⟨k, intersection_update_fsHerm_neg_one, st⟩ := x
    have hg := hH (k, intersection_update_fsHerm_neg_one, st)
    have hWc : wordUS d w ((k, intersection_update_fsHerm_neg_one, st) :: l) = lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) (wordUS d w l) := rfl
    have hLc : wordLS d a ha w ((k, intersection_update_fsHerm_neg_one, st) :: l) = (letL d a ha w (k, intersection_update_fsHerm_neg_one, st)).mul (wordLS d a ha w l) := rfl
    have key : mconv (C (lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) A)) (C B) = C (lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) (wordUS d w l)) := by
      rw [← mul (conv hg hA) hB, lconv_assoc hE hg hA hB, mul hg (conv hA hB), mul hA hB, hm, ← mul hg hW]
    refine ⟨hWc ▸ conv hg hW, ?_⟩
    rw [hWc, hLc]
    cases intersection_update_fsHerm_neg_one with
    | false =>
      obtain ⟨e₁, e₂⟩ := hl0 k st
      refine ⟨lconv (letU d w (k, false, st)) A, B, conv hg hA, hB, ?_, ?_, key⟩
      · show mconv ((letL d a ha w (k, false, st)).s w) ((wordLS d a ha w l).s w) = _
        rw [e₁, hs, ← mul hg hA]
      · show mconv ((letL d a ha w (k, false, st)).t w) ((wordLS d a ha w l).t w) = _
        rw [e₂, ht, ← mul hone hB, lconv_lone_left hB]
    | true =>
      obtain ⟨e₁, e₂⟩ := hl1 k st
      refine ⟨A, lconv (letU d w (k, true, st)) B, hA, conv hg hB, ?_, ?_, ?_⟩
      · show mconv ((letL d a ha w (k, true, st)).s w) ((wordLS d a ha w l).s w) = _
        rw [e₁, hs, ← mul hone hA, lconv_lone_left hA]
      · show mconv ((letL d a ha w (k, true, st)).t w) ((wordLS d a ha w l).t w) = _
        rw [e₂, ht, ← mul hg hB]
      · rw [← mul hA (conv hg hB), ← lconv_assoc hE hA hg hB, mul (conv hA hg) hB, mul hA hg,
          hSp E a (n - a) w (C A) (C (letU d w (k, true, st))) (isHecke_ctMu _ hU _ hμ hA) (isHecke_ctMu _ hU _ hμ hg),
          ← mul hg hA]
        exact key

theorem matchLMWordSOf : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := by
  intro hS hCt hSt hSp _ E _ _ _ hE n d hd a ha w hG hN l
  have hP : w ∉ d.P := by simp [LocData.P, hG.2.1, hG.2.2.1]
  have htr : (wordLS d a ha w l).tr d.P d.one w = (wordLS d a ha w l).s w := if_neg hP
  obtain ⟨hW, A, B, -, -, hs, ht, hm⟩ := word_ct d a ha hCt hSt hSp hE hd hG hN l
  rw [htr, hs, ht, hm]
  have hμ := hG.2.2.2.2
  have hw := hG.1
  have h1 := hS E n a ha w hw (d.μ w) hμ _ hW 1 le_rfl
  have hone : IsHecke (KL n w) (lone (KL n w)) := GlobalTheory.CompanionTheory.MatchUnit.isHecke_lone_KL hE
  have e1 : lpow (KL n w) (wordUS d w l) 1 = wordUS d w l := lconv_lone_right hW
  have e2 : mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l))
      (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (lone (KL n w))) =
      ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l) := by
    rw [← hCt E n a ha w hw (d.μ w) hμ _ _ hW hone, lconv_lone_right hW]
  rw [e1] at h1
  exact e2 ▸ h1

end GlobalTheory.CompanionTheory.MatchWordS

end
end

section


theorem _root_.GlobalTheory.T.multiplicity_inert : PositivityTheory.Rg.BcB.F.MLM.MuInert := by
  first | exact @GlobalTheory.CompanionTheory.MuInertPlace.muInert | exact GlobalTheory.CompanionTheory.MuInertPlace.muInert | (intros; apply GlobalTheory.CompanionTheory.MuInertPlace.muInert <;> assumption)
end
