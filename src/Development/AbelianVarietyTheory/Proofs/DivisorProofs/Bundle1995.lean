module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle259
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle164
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1959
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047

@[expose] public section

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.XiSplit

open Formalism.L2.Host

theorem isUnitary_of_orderDvd {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) : χ.IsUnitary := by
  intro x
  have h1 : (χ.1 x) ^ n = 1 := by
    have : (χ ^ n).1 x = 1 := by rw [h]; rfl
    rw [← this]; rfl
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem inf_eq_one {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.locInf w y = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow]
    exact hx _
  show χ.1 (Formalism.L2.Host.infDiag k) = 1
  unfold Formalism.L2.Host.infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

theorem smul_eq_of_isConjPl {D : D7} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (hc : Formalism.IndefR.Lev.IsConjPl w w') :
    D.host.conj • w.asIdeal = w'.asIdeal := by
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hzv, hz⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hz.trans (GlobalTheory.TypePlaces.star_eq_conj D _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hzv
  have hmax : (D.host.conj • w.asIdeal).IsMaximal := by
    have := w.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => w.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  exact hmax.eq_of_le w'.isPrime.ne_top hle

theorem isConjPl_of_smul_eq {D : D7} {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : D.host.conj • w.asIdeal = w'.asIdeal) : Formalism.IndefR.Lev.IsConjPl w w' := fun c hc =>
  ⟨D.host.conj • c, h ▸ Ideal.smul_mem_pointwise_smul _ _ _ hc, (GlobalTheory.TypePlaces.star_eq_conj D _).symm⟩

theorem unrAt_of_inert {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    (L.xiH t).UnrAt P := by
  obtain ⟨q, -, hI, hqP⟩ := hP
  have hfix : D.host.conj • P.asIdeal = P.asIdeal := hI P.asIdeal P.isPrime P.ne_bot hqP
  by_contra h
  rcases (hL.Q_ram t P).1 h with hPQ | ⟨P', hP', hc⟩
  · exact ((hL.Q_pl t) P hPQ).2 P hPQ (isConjPl_of_smul_eq hfix)
  · have e1 := (smul_eq_of_isConjPl hc).trans hfix.symm
    have e2 : P'.asIdeal = P.asIdeal := by
      simpa using congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) e1
    have e3 : P' = P := HeightOneSpectrum.ext e2
    subst e3
    exact ((hL.Q_pl t) P' hP').2 P' hP' hc

theorem exists_heckeU_xi : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ t : T,
    ∃ χ : HeckeU D 0, (∀ x, χ.f x = (L.xiH t).1 (finIdl D x)) ∧ ∀ τ, χ.n τ = 0 := by
  intro D T L μ₀ hL t
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have hu : (L.xiH t).IsUnitary := isUnitary_of_orderDvd hn ho
  have hi : (L.xiH t).HasInf (Formalism.L2.Host.embTau D) 0 := fun k => by
    rw [inf_eq_one hn ho k]
    simp
  have hp : ∀ τ, Even ((0 : D.what₂.Tau → ℤ) τ - ((0 : ℕ) : ℤ)) := fun τ => by simp
  have hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) →
      (L.xiH t).1 (finIdl D u) = 1 := by
    obtain ⟨M, hM, h⟩ := GlobalTheory.Mem.HeckeLevel.exists_level_nat D.host.E (L.xiH t)
    refine ⟨M, hM, fun u hu ⟨s, hs, e⟩ => h _ (GlobalTheory.Mem.Col2.SplitChar.finIdl_unit hu)
      (fun w => by rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_fst]; rfl) fun P => ?_⟩
    rw [GlobalTheory.Mem.Col2.SplitChar.vl_sub_one, e, map_mul, GlobalTheory.Mem.Col2.SplitChar.vl_nat,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact mul_le_of_le_one_right' (GlobalTheory.Mem.Col2.SplitChar.vl_le hs P)
  have hnorm := GlobalTheory.NuCharNorm.chi_norm_one D (L.xiH t) (hL.xi_triv t)
    (GlobalTheory.Mem.HeckeLevel.exists_level_nat D.host.E (L.xiH t))
  have hr := GlobalTheory.UnrKill.unr_kill D (L.xiH t) (unrAt_of_inert hL t)
  exact ⟨GlobalTheory.SplitCharGen.ofHChar 0 (L.xiH t) 0 hu hi hp hc hnorm hr, fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.XiSplit
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.InvTransposeTwist

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_invTranspose (n : ℕ) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (GlobalTheory.TypeTame.invTranspose n g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  ext
  simp [GlobalTheory.TypeTame.invTranspose, Matrix.GeneralLinearGroup.det, Matrix.det_transpose]

theorem nabs_inv (x : kˣ) : GlobalTheory.SplitWeil.nabs k x⁻¹ = (GlobalTheory.SplitWeil.nabs k x)⁻¹ := by
  simp [GlobalTheory.SplitWeil.nabs]

theorem absPow_det_invTranspose (n : ℕ) (s : ℂ) (g : GL (Fin n) k) :
    detChar (Fin n) (absPow k s) (GlobalTheory.TypeTame.invTranspose n g) =
      detChar (Fin n) (absPow k (-s)) g := by
  ext
  have hp := GlobalTheory.SplitWeil.nabs_pos k (Matrix.GeneralLinearGroup.det g)
  simp only [detChar, absPow, MonoidHom.comp_apply, det_invTranspose]
  simp [nabs_inv, Complex.cpow_neg]

theorem twist_comp_invTranspose (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ) :
    (_root_.GlobalTheory.SmGL.twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n) =
      _root_.GlobalTheory.SmGL.twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))) := by
  ext g v
  simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist, MonoidHom.coe_mk, OneHom.coe_mk, absPow_det_invTranspose]

end GlobalTheory.InvTransposeTwist

theorem GlobalTheory.InvTransposeTwist.main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ), Nonempty (Representation.Equiv ((_root_.GlobalTheory.SmGL.twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n)) (_root_.GlobalTheory.SmGL.twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))))) := by
  intro k _ _ _ _ n V _ _ π s
  rw [GlobalTheory.InvTransposeTwist.twist_comp_invTranspose]
  exact ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => rfl)⟩
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.InvTransposeCusp

theorem invTranspose_invol {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    GlobalTheory.TypeTame.invTranspose n (GlobalTheory.TypeTame.invTranspose n g) = g := by
  apply Units.ext
  exact Matrix.transpose_transpose (g : Matrix (Fin n) (Fin n) R)

theorem isSupercuspidal_comp_invTranspose (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSupercuspidal π) :
    IsSupercuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  have hcont := GlobalTheory.TypeTame.continuous_invTranspose (R := k) n
  obtain ⟨hsm, hc⟩ := hs
  refine ⟨fun v => (hsm v).preimage hcont, ?_⟩
  intro v l hl
  have hl' : l ∈ smoothPart π.dual := by
    show IsOpen {g | π.dual g l = l}
    have : {g | π.dual g l = l} = (GlobalTheory.TypeTame.invTranspose n) ⁻¹'
        {g | Representation.dual (π.comp (GlobalTheory.TypeTame.invTranspose n)) g l = l} := by
      ext g
      simp [Representation.dual, map_inv, invTranspose_invol]
    rw [this]
    exact hl.preimage hcont
  obtain ⟨C, hC, hCl⟩ := hc v l hl'
  refine ⟨(GlobalTheory.TypeTame.invTranspose n) '' C, hC.image hcont, fun g hg => ?_⟩
  obtain ⟨z, hz, c, hcC, hgc⟩ := hCl (GlobalTheory.TypeTame.invTranspose n g) hg
  refine ⟨GlobalTheory.TypeTame.invTranspose n z, ?_, GlobalTheory.TypeTame.invTranspose n c, ⟨c, hcC, rfl⟩, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro h
    have := Subgroup.mem_center_iff.1 hz (GlobalTheory.TypeTame.invTranspose n h)
    have h2 := congrArg (GlobalTheory.TypeTame.invTranspose n) this
    simpa [map_mul, invTranspose_invol] using h2
  · rw [← map_mul, ← hgc, invTranspose_invol]

theorem isCuspidal_comp_invTranspose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsCuspidal π → IsCuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  intro k _ _ _ _ n V _ _ π h
  exact GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k n V _
    (isSupercuspidal_comp_invTranspose k n V π
      (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k n V π h))

end GlobalTheory.InvTransposeCusp
end

section

open Matrix

namespace GlobalTheory.PairingTraceExpansion

variable {K : Type} [Field K] {n d : ℕ}

theorem pair_eq_trace (X Y : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM X Y = trace (Xᵀ * Y) := by
  simp only [GlobalTheory.FlipMatch.pairM, trace, diag, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem pair_expand (P M : Matrix (Fin n) (Fin d) K) :
    trace (Pᵀ * M) = ∑ i : Fin n, ∑ j : Fin d, P i j * M i j := by
  simp only [trace, diag, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem main (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin d) (Fin d) K)
    (b : GL (Fin n) K) (c : GL (Fin d) K) (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K))
      (-(Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B * (↑c : Matrix (Fin d) (Fin d) K))) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  have hb : (↑b⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * (↑b : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
    rw [← transpose_mul, Units.mul_inv, transpose_one]
  have hc : (↑c : Matrix (Fin d) (Fin d) K) * (↑c⁻¹ : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv c

  have ht : ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * (↑c⁻¹ : Matrix (Fin d) (Fin d) K)ᵀ)ᵀ *
      -((↑b : Matrix (Fin n) (Fin n) K)ᵀ * A * Q * Bᵀ * (↑c : Matrix (Fin d) (Fin d) K)) =
      -((↑c⁻¹ : Matrix (Fin d) (Fin d) K) * (Pᵀ * (A * Q * Bᵀ)) * (↑c : Matrix (Fin d) (Fin d) K)) := by
    simp only [transpose_mul, transpose_transpose, Matrix.mul_neg, neg_inj, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑b⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ, hb, Matrix.one_mul]
  rw [pair_eq_trace, ht, trace_neg, trace_mul_comm, ← Matrix.mul_assoc, hc, Matrix.one_mul, pair_expand]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring

end GlobalTheory.PairingTraceExpansion
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.SplitCoord

theorem exists_at_coord : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), X.J.det ≠ 0 → Y.J.det ≠ 0 → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧ x.map (piW t) = 0 ∧
      GlobalTheory.FlipMatch.coY σ X Y t 1 1 x = Z) ∧
    (∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧ x.map (piW (t.comp σ)) = 0 ∧
      GlobalTheory.FlipMatch.coX t 1 1 x = Z) := by
  intro F E _ _ _ _ _ σ hcm n d X Y hdX hdY v t Z
  have hA : IsUnit (X.J.map t).det := by
    rw [show (X.J.map t).det = (t : E →+* Fv F v) X.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB : IsUnit (Y.J.map t)ᵀ.det := by
    rw [Matrix.det_transpose, show (Y.J.map t).det = (t : E →+* Fv F v) Y.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdY ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  constructor
  · obtain ⟨x, hat, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hcm v t (0 : Matrix (Fin n) (Fin d) (Fv F v))
      (-((X.J.map t)⁻¹ * Z * ((Y.J.map t)ᵀ)⁻¹))
    refine ⟨x, hat, h0, ?_⟩
    simp only [GlobalTheory.FlipMatch.coY, h1, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Units.val_one,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]
  · obtain ⟨x, hat, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hcm v t Z (0 : Matrix (Fin n) (Fin d) (Fv F v))
    refine ⟨x, hat, h1, ?_⟩
    simp only [GlobalTheory.FlipMatch.coX, h0, inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.SplitCoord
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.FlipOnto

theorem det_ne_zero_of_isSkew {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  intro h0
  exact h (by rw [h0, map_zero, mul_zero])

theorem det_ne_zero_of_isHerm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  intro h0
  exact h (by rw [h0, map_zero])

theorem isUnit_det_map {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] (t : E →ₐ[F] K)
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) : IsUnit (J.map t).det := by
  have : (J.map t).det = t J.det := by
    rw [← AlgHom.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [this, isUnit_iff_ne_zero]
  exact (map_ne_zero_iff _ t.toRingHom.injective).mpr hJ

theorem coX_coY_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (bb : GL (Fin n) (Fv F v)) (cc : GL (Fin d) (Fv F v)) (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW (t.comp σ)) = 0 ∧ GlobalTheory.FlipMatch.coX t bb cc z = Z) ∧
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW t) = 0 ∧ GlobalTheory.FlipMatch.coY σ X W t bb cc z = Z) := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t bb cc Z
  constructor
  · obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hB.cm v t (bb.1 * Z * cc.1ᵀ) 0
    refine ⟨u, hu, h1, ?_⟩
    have hc : cc.1ᵀ * (cc⁻¹).1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    unfold GlobalTheory.FlipMatch.coX
    rw [h0, Matrix.mul_assoc, Matrix.mul_assoc, hc, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  · have hA : IsUnit (bb.1ᵀ * X.J.map t).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]
      exact (Units.isUnit (Matrix.GeneralLinearGroup.det bb)).mul (isUnit_det_map t (det_ne_zero_of_isHerm hX))
    have hC : IsUnit ((W.J.map t)ᵀ * cc.1).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]
      exact (isUnit_det_map t (det_ne_zero_of_isSkew hW)).mul (Units.isUnit (Matrix.GeneralLinearGroup.det cc))
    obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hB.cm v t 0
      (-((bb.1ᵀ * X.J.map t)⁻¹ * Z * ((W.J.map t)ᵀ * cc.1)⁻¹))
    refine ⟨u, hu, h0, ?_⟩
    unfold GlobalTheory.FlipMatch.coY
    rw [h1]
    calc -(bb.1ᵀ * X.J.map t * -((bb.1ᵀ * X.J.map t)⁻¹ * Z * ((W.J.map t)ᵀ * cc.1)⁻¹) * (W.J.map t)ᵀ * cc.1)
        = (bb.1ᵀ * X.J.map t * (bb.1ᵀ * X.J.map t)⁻¹) * Z * (((W.J.map t)ᵀ * cc.1)⁻¹ * ((W.J.map t)ᵀ * cc.1)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
      _ = Z := by
          rw [Matrix.mul_nonsing_inv _ hA, Matrix.nonsing_inv_mul _ hC, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.FlipOnto
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.DualClassTranspose

def equivComp {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {σ : Representation ℂ H W} (φ : G →* H) (e : ρ.Equiv σ) :
    Representation.Equiv (ρ.comp φ : Representation ℂ G V) (σ.comp φ : Representation ℂ G W) :=
  Representation.Equiv.mk' ⟨e.toLinearMap, fun g => e.toIntertwiningMap.isIntertwining' (φ g)⟩ e.symm
    (fun v => e.symm_apply_apply v) (fun w => e.apply_symm_apply w)

theorem invTranspose_eq (k : Type) [Field k] (n : ℕ) :
    GlobalTheory.TypeTame.invTranspose (R := k) n = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose n k :=
  MonoidHom.ext fun _ => Units.ext rfl

theorem dualCl_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ x y : IrrGL (k := k), DualCl x y ↔ ∃ (h1 : IsSmooth (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1))) (h2 : Representation.IsIrreducible (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1))), y = IrrGL.of (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1)) h1 h2 := by
  intro k _ _ _ _ hA x y
  have hinv : ∀ n (g : GL (Fin n) k), GlobalTheory.TypeTame.invTranspose n (GlobalTheory.TypeTame.invTranspose n g) = g :=
    fun n g => GlobalTheory.TypeTame.invTranspose_invTranspose n g
  have hsm : ∀ (z : IrrGL (k := k)), IsSmooth (z.rep.comp (GlobalTheory.TypeTame.invTranspose z.1)) := fun z v =>
    (z.2.rep.smooth v).preimage (GlobalTheory.TypeTame.continuous_invTranspose z.1)
  have hirr : ∀ (z : IrrGL (k := k)), Representation.IsIrreducible (z.rep.comp (GlobalTheory.TypeTame.invTranspose z.1)) := fun z =>
    GlobalTheory.GelfandKazhdan.isIrreducible_comp _ (fun g => ⟨_, hinv _ g⟩) z.2.rep.irr

  have gk : ∀ {n : ℕ} (π : IrrRep (GL (Fin n) k)),
      Nonempty (Representation.Equiv (π.ρ.comp (GlobalTheory.TypeTame.invTranspose n) : Representation ℂ (GL (Fin n) k) π.V) (contra π.ρ)) := by
    intro n π
    rw [invTranspose_eq]
    exact GlobalTheory.GelfandKazhdan.equiv_contra k n π.V π.ρ (hA k n π.V π.ρ π.smooth π.irr) π.irr
  constructor
  · rintro ⟨n, π, π', rfl, rfl, ⟨e⟩⟩
    refine ⟨hsm _, hirr _, ?_⟩
    obtain ⟨f⟩ := gk π
    obtain ⟨r⟩ := IrrRep.nonempty_equiv_rep π

    have e2 : Representation.Equiv ((cls π).rep.comp (GlobalTheory.TypeTame.invTranspose (cls π).1) : Representation ℂ (GL (Fin n) k) _) π'.ρ :=
      (equivComp _ r).trans (f.trans e.symm)
    show (⟨n, π'.cl⟩ : IrrGL (k := k)) = _
    have : (⟨n, π'.cl⟩ : IrrGL (k := k)) = IrrGL.of π'.ρ π'.smooth π'.irr := rfl
    rw [this]
    exact IrrGL.of_eq_of.2 ⟨e2.symm⟩
  · rintro ⟨h1, h2, rfl⟩
    refine ⟨x.1, x.2.rep, ⟨_, x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1), h1, h2⟩, ?_, rfl, ?_⟩
    · exact (congrArg (Sigma.mk x.1) x.2.cl_rep).symm
    · exact gk x.2.rep

end GlobalTheory.DualClassTranspose
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.dzWedgeDzbar_sum_pow_card_eq_factorial_det_prod : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e → ∀ K : Matrix B B ℂ, (∑ a, ∑ b, K a b • sym (e a, e b) : Ev n) ^ Fintype.card B = ((Fintype.card B).factorial * K.det : ℂ) • ∏ a, sym (e a, e a) := by
  first | exact @GlobalTheory.FlagCell2.pow_card_sum_sym | exact GlobalTheory.FlagCell2.pow_card_sum_sym | (intros; apply GlobalTheory.FlagCell2.pow_card_sum_sym <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.formPart_subset_chart_eq_lintegral_image : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (s : ℤˣ) (i : A.ι) (T : Set M), MeasurableSet T → T ⊆ (A.e i).source → A.part β s T = ∫⁻ v in A.e i '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β i v)).re) := by
  first | exact @GlobalTheory.FlagCell2.part_subset_chart | exact GlobalTheory.FlagCell2.part_subset_chart | (intros; apply GlobalTheory.FlagCell2.part_subset_chart <;> assumption)
end
