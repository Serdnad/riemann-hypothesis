module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle037
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle040
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle038
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle448
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle039
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.lp_char_compatibilities : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h) (s : ℝ), (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧ (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧ a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧ (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧ (WD.lpZero (h := h)).lpChar c = WD.lpZero (h := h) ∧ (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) := by
  exact @GlobalTheory.WeilDeligne.lpChar_laws_closed
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.tempered_of_lpDim_le_one_of_unit_eigenvalues : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : WD h), a.lpDim ≤ 1 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ a.eig φ, ‖α‖ = 1) → a.tempered := by
  first | exact @GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig | exact GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig | (intros; apply GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.weilDeligneParameter_tensor_oneDim_injective : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h), c.lpDim = 1 → a.lpChar c = b.lpChar c → a = b := by
  first | exact @GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one | exact GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one | (intros; apply GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.WD

theorem lpSum_cancel_right : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (a b c : WD h), a.lpSum c = b.lpSum c → a = b := by
  intro E Ω _ _ _ _ _ A w h a b c
  induction a using ind with
  | hP n a =>
  induction b using ind with
  | hP m b =>
  induction c using ind with
  | hP k c =>
  intro hab
  rw [lpSum_mk, lpSum_mk, mk_eq_mk] at hab
  obtain ⟨e, h1, h2⟩ := hab
  let fa : Option (Weil h) → Module.End ℂ (Fin n → ℂ) := fun o => o.elim a.N a.ρ
  let fb : Option (Weil h) → Module.End ℂ (Fin m → ℂ) := fun o => o.elim b.N b.ρ
  let fc : Option (Weil h) → Module.End ℂ (Fin k → ℂ) := fun o => o.elim c.N c.ρ
  obtain ⟨e', he'⟩ := GlobalTheory.T.endomorphismFamily_direct_summand_cancellation ℂ (Option (Weil h)) (Fin n → ℂ) (Fin m → ℂ) (Fin k → ℂ)
    fa fb fc ⟨e, fun i x => by
      cases i with
      | none => exact h2 x
      | some σ => exact h1 σ x⟩
  exact sound ⟨e', fun σ v => he' (some σ) v, fun v => he' none v⟩

end GlobalTheory.WeilDeligne.WD
end

section

open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem smul_smul_mapDR (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] (c : K) (x : L) (ω : DR k K) :
    (c • x) • mapDR k K L ω = x • mapDR k K L (c • ω) := by
  rw [map_smul, smul_assoc, smul_comm]

theorem trDR_isTrDR_unique : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L],
    IsTrDR k K L (trDR k K L) ∧ ∀ T, IsTrDR k K L T → T = trDR k K L := by
  intro k K L _ _ _ _ _ _ _ _ _
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L
  have uniq : ∀ T T' : DR k L →ₗ[k] DR k K, IsTrDR k K L T → IsTrDR k K L T' → T = T' := by
    intro T T' hT hT'
    refine LinearMap.ext fun y => ?_
    obtain ⟨m, b, ω, rfl⟩ := hspan y

    simp only [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hT, hT']
  let e := Module.finBasis K L
  let n := Module.finrank K L
  let φ : (Fin n → DR k K) →ₗ[k] DR k L :=
    { toFun := fun ω => ∑ j, e j • mapDR k K L (ω j)
      map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← algebraMap_smul K c (a j), map_smul, algebraMap_smul, smul_comm] }
  have hφ : Function.Bijective φ := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro ω hω
      funext j
      exact hind n e ω e.linearIndependent hω j
    · intro y
      obtain ⟨m, b, ω, rfl⟩ := hspan y
      refine ⟨fun j => ∑ i, e.repr (b i) j • ω i, ?_⟩
      change ∑ j, e j • mapDR k K L (∑ i, e.repr (b i) j • ω i) = _

      simp only [map_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [← smul_smul_mapDR]
      rw [← Finset.sum_smul, e.sum_repr]
  let ψ := (LinearEquiv.ofBijective φ hφ).symm
  let g : (Fin n → DR k K) →ₗ[k] DR k K :=
    { toFun := fun ω => ∑ j, Algebra.trace K L (e j) • ω j
      map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_comm] }
  have ex : IsTrDR k K L (g ∘ₗ ψ.toLinearMap) := by
    intro b ω
    have hb : b • mapDR k K L ω = φ (fun j => e.repr b j • ω) := by
      change _ = ∑ j, e j • mapDR k K L (e.repr b j • ω)
      simp only [← smul_smul_mapDR]
      rw [← Finset.sum_smul, e.sum_repr]
    rw [LinearMap.comp_apply, hb]
    have : ψ (φ (fun j => e.repr b j • ω)) = fun j => e.repr b j • ω :=
      (LinearEquiv.ofBijective φ hφ).symm_apply_apply _
    rw [LinearEquiv.coe_coe, this]
    change ∑ j, Algebra.trace K L (e j) • e.repr b j • ω = _
    simp only [smul_smul, ← Finset.sum_smul]
    congr 1
    conv_rhs => rw [← e.sum_repr b]

    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  have htr : IsTrDR k K L (trDR k K L) := by
    have h : ∃ T, IsTrDR k K L T := ⟨_, ex⟩
    unfold trDR
    rw [dite_eq_left h]
    exact h.choose_spec
  exact ⟨htr, fun T hT => uniq T _ hT htr⟩

end GlobalTheory.W1
end

section

open GlobalTheory.LatHecke

theorem _root_.GlobalTheory.T.elementarySublatticesOfIndex_degrees_qBinomial : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (L : Lat O K r), subIdx 0 L = {L} ∧ subElem 0 L = {L} ∧ (∀ k, r < k → subElem k L = ∅) ∧ ∀ X : ℂ, ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * ((subElem k L).ncard : ℂ) * X ^ k = ∏ i ∈ Finset.range r, (1 - (qRes O : ℂ) ^ i * X) := by
  first | exact @GlobalTheory.LatHecke.subElem_degrees | exact GlobalTheory.LatHecke.subElem_degrees | (intros; apply GlobalTheory.LatHecke.subElem_degrees <;> assumption)
end

section

open GlobalTheory.LatHecke

theorem _root_.GlobalTheory.T.sum_alternating_card_elementarySublattices_above : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (n : ℕ) (L M : Lat O K r), 1 ≤ n → M ∈ subIdx n L → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * (({M' | M' ∈ subElem k L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) = 0 := by
  first | exact @GlobalTheory.LatHecke.sum_alt_card_subElem_ge | exact GlobalTheory.LatHecke.sum_alt_card_subElem_ge | (intros; apply GlobalTheory.LatHecke.sum_alt_card_subElem_ge <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.exists_freeSch_hom_glue_of_etale_covering : ∀ (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (T : Sieve S), T ∈ Scheme.etaleTopology S → ∀ (σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.Tr.freeSch R V ⟶ F)), (∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V), (GlobalTheory.EtC.free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) (T.downward_closed hv g)) → ∃ t : GlobalTheory.EtC.Tr.freeSch R S ⟶ F, ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v), (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ t = σ v hv := by
  first | (exact @GlobalTheory.EtC.Tr.free_hom_glue_of_covering) | (exact GlobalTheory.EtC.Tr.free_hom_glue_of_covering) | (intros; apply GlobalTheory.EtC.Tr.free_hom_glue_of_covering  <;> assumption)
end

section

open GlobalTheory.PD

theorem _root_.GlobalTheory.T.isArtinianRing_rB_quot_span_tco_of_isFinCover : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : Type) [Field F] [Algebra k F] [Algebra F K]
    [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    IsArtinianRing (rB k K x {0} ⧸ Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))) := by
  first | (exact @GlobalTheory.PD.isArtinianRing_fib_quot) | (exact GlobalTheory.PD.isArtinianRing_fib_quot) | (intros; apply GlobalTheory.PD.isArtinianRing_fib_quot  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.FibFin

variable (k : Type) [Field k] {F : Type} (K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K]
  [IsScalarTower k F K] {d : ℕ} (x : Fin (d + 1) → F)

abbrev coordIdeal : Ideal (rB k K x {0}) :=
  Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))

def incl : rA k x {0} →ₐ[k] rB k K x {0} where
  toFun a := ⟨algebraMap F K a, (integralClosure (rA k x {0}) K).algebraMap_mem a⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp
  commutes' r := by ext; simp [← IsScalarTower.algebraMap_apply]

theorem coe_incl (a : rA k x {0}) : (incl k K x a : K) = algebraMap F K a := rfl

theorem mk_incl (hpd : IsPd k x) : ∃ ε : rA k x {0} →ₐ[k] k,
    (Ideal.Quotient.mkₐ k (coordIdeal k K x)).comp (incl k K x) = (Algebra.ofId k _).comp ε := by
  obtain ⟨e, he⟩ := GlobalTheory.PD.rA_single_polyEquiv k F d x hpd 0
  refine ⟨(MvPolynomial.aeval (0 : Fin d → k)).comp e.symm.toAlgHom, ?_⟩
  have key : ((Ideal.Quotient.mkₐ k (coordIdeal k K x)).comp (incl k K x)).comp e.toAlgHom =
      ((Algebra.ofId k _).comp ((MvPolynomial.aeval (0 : Fin d → k)).comp e.symm.toAlgHom)).comp e.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    have h1 : incl k K x (e (MvPolynomial.X j)) = (⟨_, tco_mem k K x j⟩ : rB k K x {0}) := by
      apply Subtype.ext
      rw [coe_incl, he j, Fin.succAbove_zero]
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe, Ideal.Quotient.mkₐ_eq_mk]
    change Ideal.Quotient.mk _ (incl k K x (e (MvPolynomial.X j))) =
      Algebra.ofId k _ (MvPolynomial.aeval (0 : Fin d → k) (e.symm (e (MvPolynomial.X j))))
    rw [h1, AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X, Pi.zero_apply, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self (f := fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) j))
  ext a
  have := congrArg (fun φ : MvPolynomial (Fin d) k →ₐ[k] _ => φ (e.symm a)) key
  simpa using this

theorem finite_quot (h : IsFinCover k K x) : Module.Finite k (rB k K x {0} ⧸ coordIdeal k K x) := by
  haveI := h.smooth 0
  haveI : Algebra.FiniteType k (rB k K x {0} ⧸ coordIdeal k K x) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  obtain ⟨ε, hε⟩ := mk_incl k K x h.pd
  have hε' : (algebraMap k (rB k K x {0} ⧸ coordIdeal k K x)).comp ε.toRingHom =
      (Ideal.Quotient.mk (coordIdeal k K x)).comp (incl k K x).toRingHom :=
    RingHom.ext fun a => by simpa using (AlgHom.congr_fun hε a).symm
  have hcomp : (rB k K x {0}).val.toRingHom.comp (incl k K x).toRingHom = algebraMap (rA k x {0}) K :=
    RingHom.ext fun a => rfl
  haveI : Algebra.IsIntegral k (rB k K x {0} ⧸ coordIdeal k K x) := ⟨fun q => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨p, hpm, hp⟩ : IsIntegral (rA k x {0}) (b : K) := b.2
    have hq : Polynomial.eval₂ (incl k K x).toRingHom b p = 0 := by
      apply Subtype.ext
      change (rB k K x {0}).val.toRingHom (Polynomial.eval₂ (incl k K x).toRingHom b p) = (0 : K)
      rw [Polynomial.hom_eval₂, hcomp]
      exact hp
    refine ⟨p.map ε.toRingHom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hε', ← Polynomial.hom_eval₂, hq, map_zero]⟩
  exact Algebra.IsIntegral.finite

theorem fib_finite_and_sep [IsAlgClosed k] (h : IsFinCover k K x)
    (hred : IsReduced (rB k K x {0} ⧸ coordIdeal k K x)) :
    Finite (fib k K x) ∧ ∀ f : rB k K x {0}, (∀ e : fib k K x, e.1 f = 0) → f ∈ coordIdeal k K x := by
  haveI := finite_quot k K x h
  have hker : ∀ e : fib k K x, coordIdeal k K x ≤ RingHom.ker e.1 := fun e => by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact e.2 j
  let L : fib k K x → (rB k K x {0} ⧸ coordIdeal k K x →ₐ[k] k) := fun e =>
    Ideal.Quotient.liftₐ _ e.1 (fun a ha => hker e ha)
  have hL : ∀ e f, L e (Ideal.Quotient.mk _ f) = e.1 f := fun e f => rfl
  refine ⟨Finite.of_injective L fun e₁ e₂ he => Subtype.ext (AlgHom.ext fun f => by rw [← hL, ← hL, he]),
    fun f hf => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  haveI : IsArtinianRing (rB k K x {0} ⧸ coordIdeal k K x) := IsArtinianRing.of_finite k _
  have hmem : Ideal.Quotient.mk (coordIdeal k K x) f ∈ Ideal.jacobson (⊥ : Ideal (rB k K x {0} ⧸ coordIdeal k K x)) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    haveI := hm.isPrime
    haveI : Module.Finite k (_ ⧸ m) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap (Ideal.Quotient.mkₐ_surjective k m)
    haveI : Algebra.IsIntegral k (_ ⧸ m) := Algebra.IsIntegral.of_finite k _
    have hbij : Function.Bijective (algebraMap k (_ ⧸ m)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
    let ψ := (AlgEquiv.ofBijective (Algebra.ofId k (_ ⧸ m)) hbij).symm
    let χ := (ψ.toAlgHom.comp (Ideal.Quotient.mkₐ k m)).comp (Ideal.Quotient.mkₐ k (coordIdeal k K x))
    have hχ : ∀ j : Fin d, χ ⟨_, tco_mem k K x j⟩ = 0 := fun j => by
      have hz : Ideal.Quotient.mkₐ k (coordIdeal k K x) ⟨_, tco_mem k K x j⟩ = 0 := by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.2
          (Ideal.subset_span (Set.mem_range_self (f := fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) j))
      simp only [χ, AlgHom.comp_apply, hz, map_zero]
    have h0 : ψ (Ideal.Quotient.mk m (Ideal.Quotient.mk (coordIdeal k K x) f)) = 0 := hf ⟨χ, hχ⟩
    rw [map_eq_zero_iff _ ψ.injective, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact h0
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := rB k K x {0} ⧸ coordIdeal k K x)
  have hpow : (Ideal.Quotient.mk (coordIdeal k K x) f) ^ n = 0 := by
    have := Ideal.pow_mem_pow hmem n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  exact IsNilpotent.eq_zero ⟨n, hpow⟩

end GlobalTheory.PD.FibFin
end
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.splits_pullbackSnd_of_splits_diagonalComplement : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (v : V ⟶ Z), GlobalTheory.EtC.Tr.Splits (GlobalTheory.EtC.Tr.diagComplHom f) v → GlobalTheory.EtC.Tr.Splits (pullback.snd f f) v := by
  first | exact @GlobalTheory.EtC.Tr.splits_pullbackSnd_of_splits_diagComplHom | exact GlobalTheory.EtC.Tr.splits_pullbackSnd_of_splits_diagComplHom | (intros; apply GlobalTheory.EtC.Tr.splits_pullbackSnd_of_splits_diagComplHom <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.splitBy_baseChange' : ∀ {Z X V T : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)}, GlobalTheory.EtC.Tr.SplitBy f y s → ∀ (w : T ⟶ V), GlobalTheory.EtC.Tr.SplitBy f (w ≫ y) (fun j => w ≫ s j) := by
  first | (exact @GlobalTheory.EtC.Tr.splitBy_baseChange) | (exact GlobalTheory.EtC.Tr.splitBy_baseChange) | (intros; apply GlobalTheory.EtC.Tr.splitBy_baseChange  <;> assumption)
end
