module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle428
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import GroundTheory.GlobalFields.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle490
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.AbW
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.pstRes :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O) (Bw' : LocBridge l K Ω (_root_.ReciprocityTheory.Gal.Dec (F := K) A) O),
        Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)), IsPstAt (Loc.PP l) Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) →
        IsPstAt (Loc.PP l) Bw' ((r.comp (AlgEquiv.restrictScalarsHom F : _root_.Formalism.ConjugateSelfDual.G K Ω →* _root_.Formalism.ConjugateSelfDual.G F Ω)).comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype) := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A O _ _ _ Bw Bw' hK hj hL n r hr
  obtain ⟨Kw', j', jE', jd', e', ec', esc', ecomm', LL0', hs', eO', h1', h2', h3'⟩ := Bw'
  dsimp only at hK hj hL
  subst hK hj hL
  obtain ⟨LL', r', ⟨hle, hmap⟩, hpst⟩ := hr
  refine ⟨LL', r'.comp (e'.trans Bw.e.symm).toMonoidHom, ⟨hle, ?_⟩, ?_⟩
  · refine MonoidHom.ext fun g => ?_
    have h1 := DFunLike.congr_fun hmap (Bw.e.symm (e' g))
    have h2 : ((Bw.e.symm (e' g) : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A)) : Ω ≃ₐ[F] Ω) =
        AlgEquiv.restrictScalarsHom F (g : Ω ≃ₐ[K] Ω) := by
      refine AlgEquiv.ext fun x => Bw.j.injective ?_
      rw [← Bw.e_comm, MulEquiv.apply_symm_apply, ecomm']
      rfl
    refine h1.trans ?_
    exact congrArg r h2
  · convert hpst using 1
    refine MonoidHom.ext fun g => ?_
    simp [LocBridge.repE]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

private theorem dense_of_approx {F K : Type} [Field F] [Field K] [NumberField K] (f : F →+* K)
    (w : HeightOneSpectrum (𝓞 K))
    (H : ∀ k a : K, a ≠ 0 → ∃ x : F, w.valuation K ((f x - k) / a) ≤ 1) :
    DenseRange fun x : F => algebraMap K (w.adicCompletion K) (f x) := by
  have hd := HeightOneSpectrum.denseRange_algebraMap K w
  refine Dense.of_closure (hd.mono ?_)
  rintro _ ⟨k, rfl⟩
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := by simp [c]
  obtain ⟨a, ha⟩ := w.valuation_surjective K (c * WithZero.exp (-1 : ℤ))
  have ha1 : w.valuation K a ≠ 0 := by rw [ha]; exact mul_ne_zero hc0 WithZero.exp_ne_zero
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha1
  obtain ⟨x, hx⟩ := H k a ha0
  refine ⟨_, hγ ?_, x, rfl⟩
  rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ha1), ha] at hx
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc, ← map_sub]
  have h1 : (Valued.v (algebraMap K (w.adicCompletion K) (f x - k)) : WithZero (Multiplicative ℤ)) =
      w.valuation K (f x - k) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  rw [h1]
  refine hx.trans_lt ?_
  refine mul_lt_of_lt_one_right (zero_lt_iff.2 hc0) ?_
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

private theorem surj_of_dense {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] (f : F →+* K)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (hv : ∀ x : F, w.valuation K (f x) ≤ 1 → v.valuation F x ≤ 1)
    (hd : DenseRange fun x : F => algebraMap K (w.adicCompletion K) (f x))
    (κ : v.adicCompletion F →+* w.adicCompletion K) (hc : Continuous κ)
    (hκ : ∀ x, κ (algebraMap F _ x) = algebraMap K _ (f x)) : Function.Surjective κ := by
  have hcomp : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
  have hcl := (hcomp.image hc).isClosed
  have ho : IsOpen (w.adicCompletionIntegers K : Set (w.adicCompletion K)) := Valued.isOpen_valuationSubring _
  have key : (w.adicCompletionIntegers K : Set (w.adicCompletion K)) ⊆ κ '' (v.adicCompletionIntegers F) := by
    refine (Dense.open_subset_closure_inter hd ho).trans (closure_minimal ?_ hcl)
    rintro _ ⟨h1, x, rfl⟩
    refine ⟨algebraMap F _ x, ?_, hκ x⟩
    have h2 : (Valued.v (algebraMap K (w.adicCompletion K) (f x)) : WithZero (Multiplicative ℤ)) =
      w.valuation K (f x) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have h3 : (Valued.v (algebraMap F (v.adicCompletion F) x) : WithZero (Multiplicative ℤ)) =
      v.valuation F x := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
    rw [h3]
    exact hv x (h2 ▸ h1)
  intro y
  rcases (w.adicCompletionIntegers K).mem_or_inv_mem y with h | h
  · obtain ⟨x, -, hx⟩ := key h
    exact ⟨x, hx⟩
  · obtain ⟨x, -, hx⟩ := key h
    exact ⟨x⁻¹, by rw [map_inv₀, hx, inv_inv]⟩

theorem UpperTheory.V.Af.Cq.exPlaceIso :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O),
        Induces Bw → (∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1) → ∃ (w : HeightOneSpectrum (𝓞 K)) (_ : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
          (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A v h O _ _ _ Bw hj hK
  obtain ⟨w, hw⟩ := place_between (L := K) h
  obtain ⟨κ, hκc, hκ⟩ := GlobalTheory.CompositumCompletion.exists_completion_map (algebraMap F K) v w (fun x => by
    rw [← hw, ← h x]
    show A.valuation (algebraMap K Ω (algebraMap F K x)) < 1 ↔ _
    rw [← IsScalarTower.algebraMap_apply])
  have hd := dense_of_approx (algebraMap F K) w (fun k a ha => by
    have hpos : 0 < ‖Bw.j (algebraMap K Ω a)‖ := by simpa using ha
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (Bw.j_dense (hK k)) _ hpos
    refine ⟨x, ?_⟩
    rw [← TraceCompl.algebraMap_mem_iff hw, hj, map_div₀, map_div₀, norm_div, div_le_one hpos, map_sub, map_sub,
      ← IsScalarTower.algebraMap_apply, ← dist_eq_norm, dist_comm]
    exact hx.le)
  have hs := surj_of_dense (algebraMap F K) v w (fun x hx => by
    rw [← TraceCompl.algebraMap_mem_iff hw, ← IsScalarTower.algebraMap_apply,
      TraceCompl.algebraMap_mem_iff h] at hx
    exact hx) hd κ hκc hκ
  exact ⟨w, hw, RingEquiv.ofBijective κ ⟨κ.injective, hs⟩, fun _ => Iff.rfl,
    fun x => IsScalarTower.algebraMap_apply F K Ω x, hκc, hκ⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.recTransport :
    GlobalTheory.Published.LocalLanglandsGL → ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω]
                 [IsAlgClosure F Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v)
                 (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) j i →
                 ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (v.adicCompletion F))) (σ' : SmIrr (GL (Fin n) (w.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V),
                   (∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) → ∀ rc rc', IsRec h rc → IsRec h' rc' →
                   ∀ y : WD h, WDRel (RingEquiv.refl Ω) y (rc' (algNorm σ')) → y = rc (algNorm σ) := by
  intro hL F K Ω _ _ _ _ _ _ _ _ _ A v w h h' j i P n σ σ' e he rc rc' hrc hrc' y hy
  obtain ⟨S, hS, -, -, -, -, hSt, -⟩ := GlobalTheory.WDTransport.exists_equiv_wd F Ω A v h K Ω A w h' (RingEquiv.refl Ω) j i P
  have hF := hL.2 F Ω A v h K Ω A w h' rc rc' hrc hrc' (RingEquiv.refl Ω) j i P.mem P.ext P.cont P.loc n
    { V := σ.V, ρ := σ.ρ, smooth := σ.smooth, irr := σ.irred }
    { V := σ'.V, ρ := σ'.ρ, smooth := σ'.smooth, irr := σ'.irred } e he
  have h1 : S (rc (IrrGL.of σ.ρ σ.smooth σ.irred)) = rc' (IrrGL.of σ'.ρ σ'.smooth σ'.irred) :=
    (hS _ _).1 ⟨n, hF⟩
  apply S.injective
  rw [(hS _ _).1 hy, rec_algNorm hrc, rec_algNorm hrc', hSt, h1]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sf_isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem sf_quadChar_order (E : Type) [Field E] [NumberField E] [IsCMField E] : (quadChar E).OrderDvd 2 := by
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
  rw [← map_pow, Int.units_sq, map_one]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.embPadic :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], Nonempty (K →+* ℚ_[l]) → ∀ (j : K →+* Om l) (x : K),
        j x ∈ Set.range (algebraMap ℚ_[l] (Om l)) := by
  intro K _ _ hK l _ hι j x
  obtain ⟨ι⟩ := hι
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hmon : (minpoly ℚ x).Monic := minpoly.monic hint
  have hdle : (minpoly ℚ x).natDegree ≤ 2 := hK ▸ minpoly.natDegree_le x
  have hdpos : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hint
  have hroot : ∀ f : K →+* Om l, Polynomial.aeval (f x) (minpoly ℚ x) = 0 := by
    intro f
    rw [show f x = f.toRatAlgHom x from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hy := hroot j
  have hw := hroot ((algebraMap ℚ_[l] (Om l)).comp ι)
  have hlead : (minpoly ℚ x).coeff (minpoly ℚ x).natDegree = 1 := hmon
  rw [Polynomial.aeval_eq_sum_range] at hy hw
  obtain hd | hd : (minpoly ℚ x).natDegree = 1 ∨ (minpoly ℚ x).natDegree = 2 := by omega
  · rw [hd] at hy hlead
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Rat.smul_def, pow_zero, pow_one,
      mul_one, zero_add, hlead, Rat.cast_one, one_mul] at hy
    refine ⟨-((minpoly ℚ x).coeff 0 : ℚ_[l]), ?_⟩
    rw [map_neg, map_ratCast]
    linear_combination -hy
  · rw [hd] at hy hw hlead
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Rat.smul_def, pow_zero, pow_one,
      mul_one, zero_add, hlead, Rat.cast_one, one_mul, RingHom.comp_apply] at hy hw
    have hfac : (j x - algebraMap ℚ_[l] (Om l) (ι x)) *
        (j x + algebraMap ℚ_[l] (Om l) (ι x) + ((minpoly ℚ x).coeff 1 : Om l)) = 0 := by
      linear_combination hy - hw
    rcases mul_eq_zero.1 hfac with h | h
    · exact ⟨ι x, (sub_eq_zero.1 h).symm⟩
    · refine ⟨-(ι x) - ((minpoly ℚ x).coeff 1 : ℚ_[l]), ?_⟩
      rw [map_sub, map_neg, map_ratCast]
      linear_combination -h
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.exBridge :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O), (∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1) →
        ∃ Bw' : LocBridge l K Ω (_root_.ReciprocityTheory.Gal.Dec (F := K) A) O, Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A O _ _ _ Bw hK
  haveI : IsGalois K Ω := {}
  haveI : IsGalois F Ω := {}
  haveI : T2Space (_root_.Formalism.ConjugateSelfDual.G F Ω) := krullTopology_t2
  let r : _root_.Formalism.ConjugateSelfDual.G K Ω →* _root_.Formalism.ConjugateSelfDual.G F Ω := AlgEquiv.restrictScalarsHom F
  have hr : Continuous r := continuous_restrictScalarsHom F K Ω
  have hinj : Function.Injective r := fun a b h => AlgEquiv.ext fun x => congrArg (fun g : _root_.Formalism.ConjugateSelfDual.G F Ω => g x) h
  have hind : Topology.IsInducing r := (hr.isClosedEmbedding hinj).isInducing
  have hmem : ∀ σ : _root_.Formalism.ConjugateSelfDual.G K Ω, σ ∈ _root_.ReciprocityTheory.Gal.Dec (F := K) A ↔ r σ ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A := fun σ => by
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  have hfix : ∀ (g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A)) (x : K), (g : _root_.Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) = algebraMap K Ω x := fun g x => by
    apply Bw.j.injective
    rw [← Bw.e_comm]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Bw.e g).2 _ (hK x)
  let f : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) →* ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A) :=
    (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype).codRestrict _ fun σ => (hmem σ).1 σ.2
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (hinj (congrArg Subtype.val h)), fun g => ?_⟩
    let σ : _root_.Formalism.ConjugateSelfDual.G K Ω := AlgEquiv.ofRingEquiv (f := (g : _root_.Formalism.ConjugateSelfDual.G F Ω).toRingEquiv) (hfix g)
    have hσ : r σ = g := AlgEquiv.ext fun _ => rfl
    exact ⟨⟨σ, (hmem σ).2 (hσ ▸ g.2)⟩, Subtype.ext hσ⟩
  let φ : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) ≃* ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A) := MulEquiv.ofBijective f hf
  have hφ : Continuous φ := (hr.comp continuous_subtype_val).subtype_mk _
  have hφs : Continuous φ.symm := by
    rw [(hind.comp Topology.IsInducing.subtypeVal).continuous_iff]
    exact continuous_subtype_val.congr fun g => (congrArg Subtype.val (φ.apply_symm_apply g)).symm
  refine ⟨{ Kw := Bw.Kw, j := Bw.j, j_E := hK, j_dense := ?_, e := φ.trans Bw.e
            e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
            e_comm := fun g x => Bw.e_comm (φ g) x
            LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
            eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }, rfl, rfl, rfl⟩
  refine Bw.j_dense.trans (closure_mono ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨algebraMap F K x, by simp only [← IsScalarTower.algebraMap_apply]⟩
end
