module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle380
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle294
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle394
public import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosocles
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle664
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle350
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle364
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle672
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle667
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle670
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplication
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle676
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle290
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle668
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle483
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem mul_eq_mul_diagonal_of_comm {R : Type} [CommRing R] {n r : ℕ} {G : Matrix (Fin n) (Fin n) R}
    {C : Matrix (Fin n) (Fin r) R} {L : Matrix (Fin r) (Fin n) R} (hL : L * C = 1)
    (hc : ∀ i, G * Matrix.vecMulVec (fun k => C k i) (L i) = Matrix.vecMulVec (fun k => C k i) (L i) * G) :
    G * C = C * Matrix.diagonal (fun i => (L * (G * C)) i i) := by
  ext k i
  have h := congrArg (fun M => (M * C) k i) (hc i)
  simp only [Matrix.mul_assoc, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_apply] at h
  have h1 : (L i ᵥ* C) i = 1 := by
    have := congrFun (congrFun hL i) i
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this
  rw [h1, mul_one] at h
  rw [Matrix.mul_diagonal, ← Matrix.mul_assoc]
  simpa [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct] using h

theorem mem_leviMin_of_comm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) = (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ leviMin σ J X Y ∧ γ ∈ minParOne σ J X := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW γ hγ hcomm
  have hF := pfrA h hJ hW
  have hinj : Function.Injective (inclR (F := F) (AF F) : E → AF F ⊗[F] E) := fun a b hab =>
    congrFun (GlobalTheory.CompanionTheory.RedCov.ratV_injective (F := F) (E := E) (n := 1)
      (show ratV F (fun _ : Fin 1 => a) = ratV F (fun _ : Fin 1 => b) from funext fun _ => hab)) 0
  have key : ∀ p ∈ ratPts σ J, ∃ M : Matrix (Fin n) (Fin n) E,
      (matHom _ σ J p).1 = M.map (inclR (F := F) (AF F)) := by
    intro p hp
    have hp2 : (p.1 : GL (Fin n) (AF F ⊗[F] E)) ∈
        Subgroup.map (Formalism.UG.bc (inclR (F := F) (AF F))) (Formalism.UG.UJ (σ : E →+* E) J) := hp
    obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 hp2
    refine ⟨g.1, ?_⟩
    rw [show (matHom _ σ J p).1 = ((p.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) _) from rfl, ← hg]
    rfl
  have bmRat : ∀ p ∈ ratPts σ J, ∃ M : Matrix (Fin r) (Fin r) E,
      Bm σ J X Y p = M.map (inclR (F := F) (AF F)) := by
    intro p hp
    obtain ⟨M, hM⟩ := key p hp
    refine ⟨cT (σ : E →+* E) Y * J * (M * X), ?_⟩
    rw [Bm, coefM, hM, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, PositivityTheory.ThKR.cT_map_inclR]
    rfl
  have hrow : ∀ C : Matrix (Fin n) (Fin r) E,
      cT (sigR (AF F) σ) (adMat F C) * JR (AF F) J = (cT (σ : E →+* E) C * J).map (inclR (F := F) (AF F)) := by
    intro C
    rw [Matrix.map_mul, PositivityTheory.ThKR.cT_map_inclR]
    rfl
  have hP : ∀ (C D : Matrix (Fin n) (Fin r) E) (i : Fin r),
      (lineProj σ J C D i).map (inclR (F := F) (AF F)) =
        Matrix.vecMulVec (fun k => adMat F C k i)
          ((cT (sigR (AF F) σ) (adMat F D) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) i) := by
    intro C D i
    rw [hrow]
    ext a b
    simp only [lineProj, rowOf, Matrix.vecMulVec_apply, Matrix.map_apply, adMat, map_mul]
  have hX := mul_eq_mul_diagonal_of_comm (G := (matHom _ σ J γ).1) hF.yx (fun i => by
    have := hcomm (Sum.inl i)
    rwa [projFam, Sum.elim_inl, hP] at this)
  have hY := mul_eq_mul_diagonal_of_comm (G := (matHom _ σ J γ).1) hF.xy (fun i => by
    have := hcomm (Sum.inr i)
    rwa [projFam, Sum.elim_inr, hP] at this)
  refine ⟨⟨_, _, hX, hY⟩, ⟨Matrix.diagonal _, Matrix.blockTriangular_diagonal _, hX, fun i => ?_⟩⟩
  have hp : γ ∈ minPar σ J X := ⟨_, Matrix.blockTriangular_diagonal _, hX⟩
  have hp' := inv_mem_minPar h hJ hW hp
  refine ⟨uU σ J X Y h hJ hW hp hp' i, ?_, ?_⟩
  · rw [val_uU h hJ hW hp hp' i, Bm_eq hF hX]
  · obtain ⟨M, hM⟩ := bmRat γ hγ
    obtain ⟨M', hM'⟩ := bmRat γ⁻¹ (inv_mem hγ)
    have hu1 : ((uU σ J X Y h hJ hW hp hp' i : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (F := F) (AF F) (M i i) := by
      rw [val_uU h hJ hW hp hp' i, hM]
      rfl
    have hu2 : (((uU σ J X Y h hJ hW hp hp' i)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (F := F) (AF F) (M' i i) := by
      show Bm σ J X Y γ⁻¹ i i = _
      rw [hM']
      rfl
    have he : M i i * M' i i = 1 := hinj (by rw [map_mul, ← hu1, ← hu2, Units.mul_inv, map_one])
    have he' : M' i i * M i i = 1 := by rw [mul_comm]; exact he
    have hu : uU σ J X Y h hJ hW hp hp' i =
        Units.map (inclR (F := F) (E := E) (AF F) : E →* AF F ⊗[F] E) ⟨M i i, M' i i, he, he'⟩ :=
      Units.ext (by rw [hu1]; rfl)
    rw [hu]
    exact GlobalTheory.Doubling.absE_inclR _

end GlobalTheory.CompanionTheory.ParCocompact

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SquareIntegrableSegments

theorem length_le_one_of_partial_products {h : ℕ} (d e f : Fin h → ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hd : ∀ i, 0 < d i) (he : Antitone e) (hf : ∀ i, f i = q ^ (d i * e i))
    (hpart : ∀ j : Fin h, j.val + 1 < h → ∏ i ∈ Finset.univ.filter (· ≤ j), f (Fin.rev i) < 1)
    (hfull : ∏ i, f (Fin.rev i) = 1) : h ≤ 1 := by
  by_contra hh
  have h2 : 2 ≤ h := by omega
  have hlog : Real.log q ≠ 0 := (Real.log_neg hq0 hq1).ne
  have hprod : ∀ s : Finset (Fin h), ∏ i ∈ s, f i = q ^ (∑ i ∈ s, d i * e i) := fun s => by
    rw [Real.rpow_sum_of_pos hq0]
    exact Finset.prod_congr rfl fun i _ => hf i
  have htot : ∑ i, d i * e i = 0 := by
    have h1 : ∏ i, f i = 1 := by
      rw [← hfull]
      exact (Equiv.prod_comp Fin.revPerm f).symm
    rw [hprod] at h1
    have h3 := congrArg Real.log h1
    rw [Real.log_rpow hq0, Real.log_one] at h3
    exact (mul_eq_zero.1 h3).resolve_right hlog
  obtain ⟨j, hj0, hj⟩ := GlobalTheory.CompanionTheory.Inequalities.weighted_antitone_last_nonpos h d e h2 hd he htot
  have hlt := hpart (Fin.rev j) (by have := j.isLt; rw [Fin.val_rev]; omega)
  have hrw := GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev h f (Fin.rev j)
  rw [Fin.rev_rev] at hrw
  rw [hrw, hprod] at hlt
  exact absurd hlt (not_lt.2 (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq0 hq1.le hj))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deg_eq_of_isLSeg {Δ : Segment k} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsLSeg Δ π) : Δ.deg = N := by
  obtain ⟨hd, -⟩ := h
  rw [← hd, Segment.sum_term_fst]

theorem sum_deg_of_listing {h : ℕ} {D : Fin h → Segment k} {𝔪 : Multiset (Segment k)}
    (hD : Finset.univ.val.map D = 𝔪) : ∑ i, (D i).deg = (𝔪.map Segment.deg).sum := by
  rw [← hD, Multiset.map_map]
  rfl

theorem exists_class (hE : Zc.LSegExists k) (Δ : Segment k) : ∃ y : IrrGL (k := k), IsLSeg Δ y.rep := by
  obtain ⟨π, hd, hc⟩ := hE Δ
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, hd,
    hc.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (Representation.Equiv.refl _)⟩

theorem card_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type}
      [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible →
        IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := by
  intro k _ _ _ _ hS hC hE 𝔪 N V _ _ π hN hsm hirr hsq hL
  choose y hy using exists_class hE
  have hdeg : ∀ Δ, (y Δ).1 = Δ.deg := fun Δ => (deg_eq_of_isLSeg (hy Δ)).symm
  have hpos : ∀ Δ, 0 < (y Δ).1 := fun Δ => by
    rw [hdeg]
    exact Nat.mul_pos Δ.len_pos Δ.d_pos
  choose s hs using fun Δ => GlobalTheory.T.central_character_norm_eq_pow k (y Δ) (hpos Δ)
  obtain ⟨h, D, hD, hanti, hno⟩ := GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing 𝔪 s Segment.Precedes
    fun a b hab => GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg k a b (y a) (y b) (s a) (s b) (hy a) (hy b) (hs a) (hs b) hab
  let x : Fin h → IrrGL (k := k) := fun i => y (D i)
  have hLF : LFactors 𝔪 x := ⟨D, ⟨hD, hno⟩, fun i => hy (D i)⟩
  have hsum : ∑ a, (x a).1 = N := by
    obtain ⟨h', x', hd', ⟨D', ⟨hD', -⟩, hx'⟩, -⟩ := hL
    rw [← hd']
    have e1 : ∑ a, (x a).1 = ∑ a, (D a).deg := Finset.sum_congr rfl fun a _ => hdeg (D a)
    have e2 : ∑ a, (x' a).1 = ∑ a, (D' a).deg :=
      Finset.sum_congr rfl fun a _ => (deg_eq_of_isLSeg (hx' a)).symm
    rw [e1, e2, sum_deg_of_listing hD, sum_deg_of_listing hD']
  have hsumrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hsum]
    exact Equiv.sum_comp Fin.revPerm fun a => (x a).1
  have hsoc := hS 𝔪 h N x hsumrev hLF π hL
  have hposrev : ∀ a, 0 < ((x ∘ Fin.rev) a).1 := fun a => hpos _
  have hjm := GlobalTheory.T.jacquet_multiplicity_pos_of_socle k h N (x ∘ Fin.rev) hsumrev π hsm hposrev hsoc
  have hex := hC N π hN hsm hirr hsq h (x ∘ Fin.rev) hsumrev hposrev hjm
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have hnabs := GlobalTheory.T.norm_lt_one_of_pow_tendsto_zero k t ht
  choose c hc using fun i => GlobalTheory.T.central_character_exists k (x i) t
  obtain ⟨hpart, hfull⟩ := hex t ht (c ∘ Fin.rev) fun i => hc (Fin.rev i)
  have hle : h ≤ 1 := length_le_one_of_partial_products (fun i => ((x i).1 : ℝ)) (fun i => s (D i))
    (fun i => ‖c i‖) (nabs_pos' k t) hnabs (fun i => by exact_mod_cast hpos (D i)) hanti
    (fun i => hs (D i) t (c i) (hc i)) hpart hfull
  have hh0 : h ≠ 0 := by
    rintro rfl
    simp at hsum
    omega
  have hcard : 𝔪.card = h := by
    rw [← hD]
    simp
  omega

end GlobalTheory.CompanionTheory.SquareIntegrableSegments
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.LSocle

section General

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSmooth_of_surjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : IsSmooth σ := by
  intro w
  obtain ⟨v, rfl⟩ := hf w
  let S : Subgroup G :=
    { carrier := {g | σ g (f v) = f v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : σ a⁻¹ (σ a (f v)) = f v := by
          rw [← Module.End.mul_apply, ← map_mul]; simp
        rwa [ha] at h1 }
  let T : Subgroup G :=
    { carrier := {g | ρ g v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ρ a⁻¹ (ρ a v) = v := by
          rw [← Module.End.mul_apply, ← map_mul]; simp
        rwa [ha] at h1 }
  have hT : IsOpen (T : Set G) := hρ v
  have hTS : T ≤ S := fun g hg => by
    have hg' : ρ g v = v := hg
    show σ g (f v) = f v
    rw [← f.isIntertwining, hg']
  exact Subgroup.isOpen_mono hTS hT

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thetaW_surjective (N : ℕ) : Function.Surjective (thetaW k N) :=
  fun g => ⟨thetaW k N g, GlobalTheory.T.transpose_inverse_involution_apply N g⟩

theorem comp_thetaW_thetaW {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) : (π.comp (thetaW k N)).comp (thetaW k N) = π :=
  MonoidHom.ext fun g => by
    show π (thetaW k N (thetaW k N g)) = π g
    rw [GlobalTheory.T.transpose_inverse_involution_apply N g]

theorem isCosocle_comp_thetaW {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin N) k) W} {π : Representation ℂ (GL (Fin N) k) V}
    (h : IsCosocle σ (π.comp (thetaW k N))) : IsCosocle (σ.comp (thetaW k N)) π := by
  apply GlobalTheory.FieldTransport.isCosocle_of_comp (thetaW_surjective N)
  show IsCosocle ((σ.comp (thetaW k N)).comp (thetaW k N)) _
  rw [comp_thetaW_thetaW σ]
  exact h

theorem equiv_contra_comp_thetaW (hGK : GKLocal k) {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin N) k) W) (hs : IsSmooth (σ.comp (thetaW k N)))
    (hi : Representation.IsIrreducible (σ.comp (thetaW k N))) : Nonempty (σ.Equiv (contra (σ.comp (thetaW k N)))) := by
  have E := GlobalTheory.T.gelfand_kazhdan_contragredient hGK N (σ.comp (thetaW k N)) hs hi
  rwa [comp_thetaW_thetaW σ] at E

theorem prodIrr_congr {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : x = y) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩



theorem isSocle_rev_of_isCosocle (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x y : Fin h → IrrGL (k := k)) (hd0 : ∑ a, (x a).1 = N) (hd : ∑ a, ((x ∘ Fin.rev) a).1 = N) (hdy : ∑ a, (y a).1 = N)
    (e3 : (fun a => dualCl (y (Fin.rev a))) = x) (e6 : (fun a => dualCl (y a)) = x ∘ Fin.rev)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hc : IsCosocle π (prodIrr x hd0)) : IsSocle π (prodIrr (x ∘ Fin.rev) hd) := by
  obtain ⟨hd2, ⟨E2⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK y hdy
  obtain ⟨E3⟩ := prodIrr_congr e3 hd2 hd0
  have hc1 : IsCosocle π ((prodIrr y hdy).comp (thetaW k N)) :=
    hc.of_equiv (Representation.Equiv.refl _) (E2.trans E3).symm
  have hc2 : IsCosocle (π.comp (thetaW k N)) (prodIrr y hdy) := isCosocle_comp_thetaW hc1
  have hs : IsSmooth (π.comp (thetaW k N)) := by
    obtain ⟨-, f, hf, -⟩ := hc2
    exact isSmooth_of_surjective (isSmooth_prodIrr y hdy) f hf
  have hsoc := GlobalTheory.T.cosocle_contragredient_socle hA (π.comp (thetaW k N)) (prodIrr y hdy) (isSmooth_prodIrr y hdy)
    (GlobalTheory.T.product_irreducible_finite_length hA y hdy) hc2
  obtain ⟨E4⟩ := equiv_contra_comp_thetaW hGK π hs hc2.1
  obtain ⟨hd5, ⟨E5⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA y hdy
  obtain ⟨E6⟩ := prodIrr_congr e6 hd5 hd
  exact hsoc.of_equiv E4.symm (E5.trans E6)

theorem lSocleGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k → LOrderFree k → LSocleGL k := by
  intro k _ _ _ _ hA hGK hLO 𝔪 h N x hd hx V _ _ π hπ
  have hd0 : ∑ a, (x a).1 = N := by
    rw [← hd]
    exact (Equiv.sum_comp Fin.revPerm (fun a => (x a).1)).symm
  have hc := hLO 𝔪 h N x hd0 hx π hπ
  obtain ⟨hdy, -⟩ := GlobalTheory.T.contragredient_product_irreducible hA (x ∘ Fin.rev) hd
  exact isSocle_rev_of_isCosocle hA hGK x (fun a => dualCl ((x ∘ Fin.rev) a)) hd0 hd hdy
    (funext fun a => by
      simp only [Function.comp_apply, Fin.rev_rev]
      exact GlobalTheory.T.dual_class_involutive hA (x a))
    (funext fun a => GlobalTheory.T.dual_class_involutive hA (x (Fin.rev a))) π hc

end GlobalTheory.CompanionTheory.LSocle
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MLM Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SepPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem zpow_mul_inj {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {a c : ℤ} {u v : w.adicCompletion E}
    (hu : Valued.v u = 1) (hv : Valued.v v = 1)
    (h : ((ϖ ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * u = ((ϖ ^ c : (w.adicCompletion E)ˣ) : w.adicCompletion E) * v) :
    a = c := by
  have e := congrArg Valued.v h
  rw [map_mul, map_mul, hu, hv, mul_one, mul_one] at e
  have h1 : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [GlobalTheory.BorelUMod.v_eq_exp ϖ.ne_zero, hϖ.1]
  have h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0 := by
    rw [h1]; exact WithZero.exp_ne_zero
  have hne : Valued.v (ϖ : w.adicCompletion E) ≠ 1 := by
    rw [h1, ← WithZero.exp_zero]
    intro h2
    have := WithZero.exp_injective h2
    omega
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀] at e
  exact zpow_right_injective₀ (zero_lt_iff.2 h0) hne e

theorem separable_of_fU {w : Pl E} {b : GLw n w} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {l : Fin (n / 2) → ℤ}
    (hl : Cone l) {γ : UL n w} (h : fU n w b ϖ l γ ≠ 0) : γ.1.val.charpoly.Separable := by
  have hy := (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).1
  have h' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := by
    by_contra hc
    exact h (if_neg hc)
  obtain ⟨x, hx, z, hz, e⟩ := h'
  obtain ⟨x', hx', ex⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
  obtain ⟨z', hz', ez⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hz)
  have ex' : x.1 = b * x' * b⁻¹ := ex.symm
  have ez' : z.1 = b * z' * b⁻¹ := ez.symm
  have hδ : dcos n w (tdiag ϖ (wexp n l)) (b⁻¹ * γ.1 * b) ≠ 0 := by
    have : ∃ p ∈ iwGL n w, ∃ q ∈ iwGL n w, b⁻¹ * γ.1 * b = p * tdiag ϖ (wexp n l) * q :=
      ⟨x', hx', z', hz', by rw [e, ex', ez']; group⟩
    simp [dcos, this]
  obtain ⟨m, -, τ, hτ, em⟩ := GlobalTheory.CompanionTheory.IwahoriContraction.contr_id w ϖ hϖ n (wexp n l) hy _ hδ
  have hval : (tdiag ϖ (wexp n l) * τ).val = Matrix.diagonal fun i =>
      ((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * τ.val i i := by
    have hτd : τ.val = Matrix.diagonal fun i => τ.val i i := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · rw [hτ.1 i j hij, Matrix.diagonal_apply_ne _ hij]
    rw [Units.val_mul, GlobalTheory.CompanionTheory.FUMulPf.tdiag_val, hτd, Matrix.diagonal_mul_diagonal]
    simp
  have hg : γ.1 = (b * m) * (tdiag ϖ (wexp n l) * τ) * (b * m)⁻¹ := by
    rw [← em]; group
  rw [GlobalTheory.CompanionTheory.UnitarySide.charpoly_conj_diagonal (b * m) _ γ.1 _ hval hg, Polynomial.separable_prod_X_sub_C_iff]
  intro i j hij
  exact hy.injective (zpow_mul_inj hϖ (hτ.2 i) (hτ.2 j) hij)

theorem sepPowT : SepPowT := by
  intro E _ _ _ hU n d hd hm m w hT y hy
  obtain ⟨hs, hb, hϖ, hx⟩ := hm.T w hT
  have hx' : ∀ j, StrictAnti (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j) ∧ Cone (lOf (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j)) :=
    fun j => hx j.1 j.2
  obtain ⟨J', _, c', x', hx'', e1, -⟩ := GlobalTheory.CompanionTheory.MatchPow.pow_claim GlobalTheory.CompanionTheory.FUMulPf.fuMul GlobalTheory.CompanionTheory.DcosProduct.dcosMul hU hs 0
    hb hϖ (GlobalTheory.CompanionTheory.MatchLMPlaces.cc d w) (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w) hx' m
  have hKU : d.KU w = iwU n w (d.b w) := by simp [LocData.KU, hT]
  have hG : d.gU (m + 1) w y = (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1) *
      (GlobalTheory.CompanionTheory.MatchPow.alpha n w (d.b w) ^ m * ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y) := by
    unfold LocData.gU
    rw [hKU, GlobalTheory.CompanionTheory.MatchLMPlaces.unitary_function_at_T d hT, GlobalTheory.CompanionTheory.MatchLMPlaces.lpow_scale, e1]
  rw [hG] at hy
  have hsum : ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y ≠ 0 := fun h0 => hy (by rw [h0]; simp)
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact separable_of_fU hϖ (hx'' j).2 (right_ne_zero_of_mul hj)

end GlobalTheory.CompanionTheory.SepPow

end
end
