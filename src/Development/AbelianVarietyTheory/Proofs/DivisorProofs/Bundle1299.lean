module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle937
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CMLatticeDividedPowerJetIntegralityOfHyp
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import ReciprocityTheory.DualLattices.Bundle010
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem KSp.sgn_mul_of_isQuad : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s t : Fˣ), sgn E (s * t) = sgn E s * sgn E t := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE s t
  set H := (Units.map (Algebra.norm F : E →* F)).range with hH
  unfold sgn
  rw [← hH]
  by_cases hs : s ∈ H <;> by_cases ht : t ∈ H
  · simp [hs, ht, H.mul_mem hs ht]
  · have : s * t ∉ H := fun h => ht ((H.mul_mem_cancel_left hs).mp h)
    simp [hs, ht, this]
  · have : s * t ∉ H := fun h => hs ((H.mul_mem_cancel_right ht).mp h)
    simp [hs, ht, this]
  · have : s * t ∈ H := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE s t hs ht
    simp [hs, ht, this]

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.BotLValue

section General

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

end General

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open Formalism.L2.Host (aboveF)

open NumberField IsDedekindDomain in
private theorem eq_or_eq_of_comp_eq_of_finrank_two {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2) (ψ : F →+* ℂ)
    (ρ α β : E →+* ℂ) (hρ : ρ.comp (algebraMap F E) = ψ) (hα : α.comp (algebraMap F E) = ψ)
    (hβ : β.comp (algebraMap F E) = ψ) (hαβ : α ≠ β) : ρ = α ∨ ρ = β := by
  classical
  letI : Algebra F ℂ := ψ.toAlgebra
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let mk : ∀ γ : E →+* ℂ, γ.comp (algebraMap F E) = ψ → E →ₐ[F] ℂ := fun γ hγ =>
    { toRingHom := γ
      commutes' := fun a => (congrArg (fun f : F →+* ℂ => f a) hγ : _) }
  have hcoe : ∀ (γ : E →+* ℂ) (hγ : γ.comp (algebraMap F E) = ψ), ((mk γ hγ : E →ₐ[F] ℂ) : E →+* ℂ) = γ :=
    fun γ hγ => rfl
  by_contra hne
  push_neg at hne
  have hcard := AlgHom.card F E ℂ
  rw [h2] at hcard
  have hfa : mk ρ hρ ≠ mk α hα := fun e => hne.1 (by rw [← hcoe ρ hρ, ← hcoe α hα, e])
  have hfb : mk ρ hρ ≠ mk β hβ := fun e => hne.2 (by rw [← hcoe ρ hρ, ← hcoe β hβ, e])
  have hab : mk α hα ≠ mk β hβ := fun e => hαβ (by rw [← hcoe α hα, ← hcoe β hβ, e])
  have h3 : ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hfa, hfb]), Finset.card_pair hab]
  have := Finset.card_le_univ ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ))
  omega


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.BotLValue.isCMType_embOver {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, _root_.GlobalTheory.AdelicU.EmbOver E w) :
    _root_.GlobalTheory.CMVal.IsCMType fun w => (τ w).1 := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt at h
  obtain ⟨hF, hE, h2, hσ⟩ := h
  unfold _root_.GlobalTheory.CMVal.IsCMType
  have hreal : ∀ v : InfinitePlace F, ComplexEmbedding.conjugate v.embedding = v.embedding :=
    fun v => ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp (hF.isReal v))
  have hconj : ∀ (v : InfinitePlace F) (γ : E →+* ℂ), γ.comp (algebraMap F E) = v.embedding →
      (ComplexEmbedding.conjugate γ).comp (algebraMap F E) = v.embedding := by
    intro v γ hγ
    rw [← hreal v, ← hγ]
    rfl
  have hτ : ∀ v : InfinitePlace F, ((τ v).1).comp (algebraMap F E) = v.embedding := fun v => (τ v).2
  have hne : ∀ v : InfinitePlace F, (τ v).1 ≠ ComplexEmbedding.conjugate (τ v).1 := by
    intro v e
    have hc := hE.isComplex (InfinitePlace.mk (τ v).1)
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff] at hc
    exact hc e.symm
  intro ρ
  set v := InfinitePlace.mk (ρ.comp (algebraMap F E)) with hvdef
  have hv : ρ.comp (algebraMap F E) = v.embedding := by
    rcases InfinitePlace.embedding_mk_eq (ρ.comp (algebraMap F E)) with e | e
    · exact e.symm
    · rw [← hreal v, e]
      exact (star_star _).symm
  refine ⟨v, eq_or_eq_of_comp_eq_of_finrank_two h2 v.embedding ρ _ _ hv (hτ v) (hconj v _ (hτ v)) (hne v), ?_⟩
  intro w hw
  have hw' : ρ.comp (algebraMap F E) = w.embedding := by
    rcases hw with e | e
    · rw [e]; exact hτ w
    · rw [e]; exact hconj w _ (hτ w)
  rw [hvdef, hw', InfinitePlace.mk_embedding]

end GlobalTheory.BotLValue

end
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivisibleGroup_datum_of_connected_dual_connected : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → GlobalTheory.PDivLat.IsConn G.dual → HasDatum hε G) → ∀ G : PDivGroup p O, HasDatum hε G := by
  first | exact @GlobalTheory.PDivLat.hasDatum_of_conn_dual_conn | exact GlobalTheory.PDivLat.hasDatum_of_conn_dual_conn | (intros; apply GlobalTheory.PDivLat.hasDatum_of_conn_dual_conn <;> assumption)
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.HodgeNat

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem theta_xi_eq_zero [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (xi ε) = 0 := by
  have h1 : IsPrimitiveRoot (zeta ε 1) p := by simpa using hε 1
  have h2 := h1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt

  rw [xi, map_sum]
  simpa [map_pow, WittVector.fontaineTheta_teichmuller, zeta] using h2

theorem ghost_mu_eq_zero [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (n : ℕ) :
    ghost p O n (Sandwich.mu ε) = 0 := by
  induction n with
  | zero =>
    show WittVector.fontaineTheta O p (Sandwich.mu ε) = 0
    rw [Sandwich.mu, map_sub, WittVector.fontaineTheta_teichmuller, map_one, sub_eq_zero]
    exact hε.zeta_zero
  | succ n ih =>
    rw [← ghost_frobenius, Dieudonne.frobenius_mu, ghost_mul, ih, mul_zero]

noncomputable def muPair [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (χ : G.dual.Tate) : TDual G where
  toFun t := Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)
  map_add' s t := by
    simp only [epsPairing, map_add (f := _), LinearMap.add_apply, mul_add]
  map_smul' a t := by
    simp only [epsPairing, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring

theorem muPair_mem [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (χ : G.dual.Tate) : muPair hε G χ ∈ latt G := fun n =>
  ⟨0, fun t => by
    show ghost p O n (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) = 0
    rw [ghost_mul, ghost_mu_eq_zero hε, zero_mul]⟩

end GlobalTheory.PDivLat.HodgeNat


open GlobalTheory.PDivLat.HodgeNat in
theorem GlobalTheory.PDivLat.iota_natural : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G H : PDivGroup p O) (f : G ⟶ H), HasDatum hε G → HasDatum hε H → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (M' : Type) [AddCommGroup M'] [Module O M'] (r' : latt H →ₛₗ[WittVector.fontaineTheta O p] M') (u : M' →ₗ[O] M) (ι : G.omega →ₗ[O] M) (ι' : H.omega →ₗ[O] M'), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ y, u (r' y) = r (lattMap f y)) → (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) → (∀ (χ : H.dual.Tate) (y : latt H), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε H t χ)) → ι' (dlog H χ) = r' y) → ∀ w, u (ι' w) = ι (omegaMap G H f w) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G H f hG hH M _ _ r M' _ _ r' u ι ι' hrs hrk hu hι hι' w
  obtain ⟨hfree, hfin, -⟩ := GlobalTheory.T.pDivisibleGroup_lattice_free_rank_height p C v O hv ε hε G hG
  haveI : Nontrivial (Ainf p O) := (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv).nontrivial
  obtain ⟨hMfree, -, -⟩ := Dieudonne.free_of_reduction (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv)
    (theta_xi_eq_zero hε) r hrs fun m hm => (hrk m).1 hm
  haveI := hMfree

  have key : ∀ χ : H.dual.Tate, u (ι' (dlog H χ)) = ι (omegaMap G H f (dlog H χ)) := by
    intro χ
    let Y : latt H := ⟨muPair hε H χ, muPair_mem hε H χ⟩
    have h1 : ι' (dlog H χ) = r' Y := hι' χ Y fun t => rfl
    have h2 : ι (dlog G (tateMap H.dual G.dual O (dualHom G H f) χ)) = r (lattMap f Y) := by
      refine hι _ _ fun t => ?_
      show Sandwich.mu ε * ofPadic p O (epsPairing hε H (tateMap G H O f t) χ) = _
      rw [epsPairing, epsPairing, pairing_tateMap]
    rw [h1, hu, ← h2, dlog_tateMap]
  obtain ⟨c, hc, hcw⟩ := GlobalTheory.T.pDivGroup_exists_smul_mem_span_dlog p C v O hv ε hε H hH
  have hspan : ∀ x ∈ Submodule.span O (Set.range (dlog H)),
      u (ι' x) = ι (omegaMap G H f x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨χ, rfl⟩ := hx; exact key χ
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have h := hspan _ (hcw w)
  simp only [map_smul] at h
  have h' : c • (u (ι' w) - ι (omegaMap G H f w)) = 0 := by rw [smul_sub, h, sub_self]
  have tf : ∀ x : M, c • x = 0 → x = 0 := by
    intro x hx
    let b := Module.Free.chooseBasis O M
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    have h3 := congrArg (fun y => b.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
    simpa using (mul_eq_zero.1 h3).resolve_left hc
  exact sub_eq_zero.1 (tf _ h')
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (S : Sys I π s₀) (S' : Sys I π t₀) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T) (hl : (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l) (hn : (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l) (L : LB X₀) (L' : LB Z₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff t₀))), L.IsLB → L'.IsLB → LBIso L' (L.pull f₀) → IsObL S α L c → IsObL S' α L' c' → IsExtendedPullbackDegTwo R₁ h c c' := by
  first | exact @GlobalTheory.LBObs.lineBundleLiftObstruction_natural_alt | exact GlobalTheory.LBObs.lineBundleLiftObstruction_natural_alt | (intros; apply GlobalTheory.LBObs.lineBundleLiftObstruction_natural_alt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.harrisTaylor_inverse_heckeTranslates_forget_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (o₁ : Obj b (N * k) s) (o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o₁.A ⟶ o₂.A), IsHecke g' c' k (N * k) o o₁ ψ₁ → IsHecke g c k N o₁ o₂ ψ₂ → Nonempty (ObjMap (o.forget N ⟨k * k, by ring⟩ hc) o₂ (𝟙 S)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget) | (exact GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget) | (intros; apply GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem theory_V_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
    (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
    Function.Injective (T.F G) ∧ Function.Injective (T.V G) ∧
      (∀ m, T.smap (frobProj (p_eq_zero p k) G) (T.V G m) = T.map (verschiebung (p_eq_zero p k) G) m) ∧
      (∀ (H : PDivGroup p k) (φ : T.M H →ₗ[WittVector p k] T.M G),
        (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m)) ∧
      ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H), T.map f (T.V H m) = T.V G (T.map f m) := by
  intro p _ T k _ _ _ G

  have tor : ∀ (K : PDivGroup p k) (m : T.M K), p • m = 0 → m = 0 := by
    intro K m hm
    exact T.base.eq_zero_of_pow_smul (G := K) trivial 1 m (by simpa only [pow_one] using hm)
  have Finj : ∀ K : PDivGroup p k, Function.Injective (T.F K) := by
    intro K x y hxy
    have h1 : p • x = p • y := by rw [← T.V_F K x, ← T.V_F K y]; exact congrArg _ hxy
    have : p • (x - y) = 0 := by rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (tor K _ this)
  have Vinj : ∀ K : PDivGroup p k, Function.Injective (T.V K) := by
    intro K x y hxy
    have h1 : p • x = p • y := by rw [← T.F_V K x, ← T.F_V K y]; exact congrArg _ hxy
    have : p • (x - y) = 0 := by rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (tor K _ this)
  have comm : ∀ (H : PDivGroup p k) (φ : T.M H →ₗ[(WittVector p k)] T.M G),
      (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m) := by
    intro H φ hφ m
    apply Finj G
    rw [← hφ, T.F_V H m, T.F_V G, map_nsmul]
  refine ⟨Finj G, Vinj G, ?_, comm, ?_⟩
  · intro m
    have ht := frobTwist_module p T.base k G
    obtain ⟨n, hn⟩ := ht.1.2 (T.map (verschiebung (p_eq_zero p k) G) m)
    have hF : T.F G n = p • m := ht.2.2 m n hn
    have : n = T.V G m := Finj G (by rw [hF, T.F_V])
    rw [← this]; exact hn
  · intro H f m
    exact comm H (T.map f) (T.base.map_F trivial trivial f) m

end GlobalTheory.Dieu
end

section

open GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius :
    ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p fun _ _ _ => True)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k),
      Function.Bijective (B.smap trivial trivial (frobProj (p_eq_zero p k) G)) ∧
      (∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
        (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m) ∧
      ∀ m n, B.smap trivial trivial (frobProj (p_eq_zero p k) G) n =
        B.map trivial trivial (verschiebung (p_eq_zero p k) G) m →
        B.F G trivial n = p • m :=
  @GlobalTheory.Dieu.frobTwist_module
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.etaleDieudonneTranspose_semilinearHom_dualGroups : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (G' : PDivGroup p k') (hd : G.dual.IsConn) (hd' : G'.dual.IsConn) (hb : (G.dual.baseChange k').IsConn) (s : SemiHom (algebraMap k k') G' G) (l : Module.Dual (WittVector p k) (B.M G.dual hd)), ∃! l' : Module.Dual (WittVector p k') (B.M G'.dual hd'), ∃ lb : Module.Dual (WittVector p k') (B.M (G.dual.baseChange k') hb), (∀ x, lb (B.smap hb hd (G.dual.toBase k') x) = WittVector.map (algebraMap k k') (l x)) ∧ ∀ y, l' y = lb (B.map hb hd' ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) y) := by
  first | exact @GlobalTheory.semiHom_dual_transpose | exact GlobalTheory.semiHom_dual_transpose | (intros; apply GlobalTheory.semiHom_dual_transpose <;> assumption)
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.HCFct

theorem exists_interp {K : Type} (W : Submodule ℂ (K → ℂ)) (hW : FiniteDimensional ℂ W) :
    ∃ (s : Finset K) (b : s → W), ∀ w ∈ W, ∀ k, w k = ∑ i : s, w i.1 * (b i).1 k := by
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.finiteDim_functions_detected_by_finset K W hW
  let ev : W →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun i =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) i.1).comp W.subtype
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hs w.1 w.2 fun k hk => congrFun hw ⟨k, hk⟩)
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective ev hev
  refine ⟨s, fun i => ψ (fun j => if i = j then 1 else 0), fun w hw k => ?_⟩
  have e1 : (⟨w, hw⟩ : W) = ψ (ev ⟨w, hw⟩) := (LinearMap.congr_fun hψ _).symm
  rw [LinearMap.pi_apply_eq_sum_univ ψ (ev ⟨w, hw⟩)] at e1
  have e2 := congrArg (fun u : W => u.1 k) e1
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ev,
    LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply] using e2

theorem constTerm_cptTranslate_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ W := by
  intro E _ _ _ a L W hW X N r _ _ μ 𝓕 hμ h𝓕 _ φ hφ g
  have hP : Continuous φ.1 ∧ (∀ γ h, φ.1 (ratGL E a γ * h) = φ.1 h) ∧
      ∀ h, (fun k : Kinf E a => φ.1 (h * infGL E a (Unitary.toUnits k))) ∈ W := by
    induction hφ using Submodule.span_induction with
    | mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left, fun h => hx.2.2.1 h⟩
    | zero => exact ⟨continuous_const, fun _ _ => rfl, fun _ => W.zero_mem⟩
    | add x y _ _ hx hy =>
      exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2.1 γ h) (hy.2.1 γ h),
        fun h => W.add_mem (hx.2.2 h) (hy.2.2 h)⟩
    | smul c x _ hx =>
      exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2.1 γ h), fun h => W.smul_mem c (hx.2.2 h)⟩
  obtain ⟨hc, hl, hK⟩ := hP
  obtain ⟨s, b, hb⟩ := exists_interp W hW
  haveI := hμ
  have hint : ∀ h, IntegrableOn (fun x => φ.1 (unip x * h)) 𝓕 μ := fun h =>
    CuspidalL2GL.integrableOn_unip hc hl μ h𝓕 h
  have hpt : ∀ k (x : BlockIx a r → Ad E), φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) =
      ∑ i : s, φ.1 (unip x * (g * infGL E a (Unitary.toUnits i.1))) * (b i).1 k := fun k x => by
    have := hb _ (hK (unip x * g)) k
    simpa only [mul_assoc] using this
  have e : (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) =
      ∑ i : s, (∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits i.1))) ∂μ) • (b i).1 := by
    funext k
    simp only [hpt k]
    rw [integral_finsetSum _ fun i _ => (hint _).mul_const _]
    simp only [integral_mul_const, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact W.sum_mem fun i _ => W.smul_mem _ (b i).2

end GlobalTheory.HCFct

end
end

section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

theorem _root_.GlobalTheory.T.shintani_formula_alt : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)) = GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * W 1 := by
  first | exact @GlobalTheory.JSW.shintani_formula | exact GlobalTheory.JSW.shintani_formula | (intros; apply GlobalTheory.JSW.shintani_formula <;> assumption)
end

section


theorem _root_.GlobalTheory.T.cmLatticeDividedPowerJetIntegrality_of_ellipticCM : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatJet.JetInt := by
  first | exact @GlobalTheory.JetIntElliptic.jetInt | exact GlobalTheory.JetIntElliptic.jetInt | (intros; apply GlobalTheory.JetIntElliptic.jetInt <;> assumption)
end
