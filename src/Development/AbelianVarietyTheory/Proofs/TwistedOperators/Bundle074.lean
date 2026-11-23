module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle071
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory

namespace GlobalTheory.InertSupp.Unram

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open ValuativeRel Matrix MeasureTheory in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.InertSupp.Unram.valuation_det_KO {m : Type} [Fintype m] [DecidableEq m] {g : GL m k}
    (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k m) :
    valuation k (GeneralLinearGroup.det g : k) = 1 := by
  unfold _root_.GlobalTheory.SplitWeil.KO at hg
  obtain ⟨h, rfl⟩ := hg
  have hdet : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap (𝒪[k]) k) h) : k)
      = algebraMap (𝒪[k]) k (GeneralLinearGroup.det h : 𝒪[k]) := by
    simp [GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [hdet]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

end GlobalTheory.InertSupp.Unram
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.MellinPoly

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_eq_zpow (s : ℂ) (x : kˣ) :
    (absPow k s x : ℂ) = ((resCard k : ℂ) ^ (-s)) ^ (SmGL.ord k x : ℤ) := by
  have hq : (0 : ℝ) < (resCard k : ℝ) := by
    unfold resCard
    exact_mod_cast Nat.card_pos
  have hq0 : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hz : (resCard k : ℝ) ^ (-SmGL.ord k x) ≠ 0 := (zpow_pos hq _).ne'
  unfold absPow
  simp only [MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [GlobalTheory.LGrp.nabs_eq_zpow, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hz),
    Complex.cpow_def_of_ne_zero hq0, ← Complex.exp_int_mul, ← Complex.ofReal_log (zpow_pos hq _).le,
    Real.log_zpow, ← Complex.ofReal_natCast, ← Complex.ofReal_log hq.le]
  push_cast
  congr 1
  ring

end GlobalTheory.MellinPoly
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open scoped TensorProduct

namespace GlobalTheory.PrinProd

theorem isSubquotient_prinSeries_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (χ : Fin N → kˣ →* ℂˣ) :
    IsSubquotient (prinSeries χ)
      (multiProd (Equiv.sigmaUnique (Fin N) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)) := by
  let e : (Σ _ : Fin N, Fin 1) ≃ Fin N := Equiv.sigmaUnique (Fin N) fun _ => Fin 1
  let κ : ℂ ≃ₗ[ℂ] ⨂[ℂ] _ : Fin N, ℂ := (PiTensorProduct.constantBaseRingEquiv (Fin N) ℂ).toLinearEquiv.symm
  let Ψ : IndSp (points (Fin N)) ((ofChar (torusChar χ)).comp (leviTorus k (Fin N)).symm.toMonoidHom) →ₗ[ℂ]
      IndSp e (piTensor fun i => detRep (Fin 1) (χ i)) :=
    MultiIrr.indPull (MonoidHom.id _) continuous_id κ.toLinearMap fun p =>
      ⟨⟨p, mem_parab_iff.2 fun a b _ _ hab => mem_parab_iff.1 p.2 a b 0 0 hab⟩, rfl, fun w => by
        have hd : ∀ a, GeneralLinearGroup.det (leviProj k e p a) =
            GeneralLinearGroup.det (leviProj k (points (Fin N))
              ⟨p, mem_parab_iff.2 fun a b _ _ hab => mem_parab_iff.1 p.2 a b 0 0 hab⟩ a) := fun a => by
          ext
          simp only [GeneralLinearGroup.val_det_apply, det_unique]
          rfl
        show (deltaHalf k _ (leviProj k e p) : ℂ) • piTensor (fun i => detRep (Fin 1) (χ i)) (leviProj k e p) (κ w) =
          κ ((deltaHalf k _ (leviProj k (points (Fin N)) _) : ℂ) •
            ofChar (torusChar χ) ((leviTorus k (Fin N)).symm (leviProj k (points (Fin N)) _)) w)
        rw [map_smul, deltaHalf_apply, deltaHalf_apply]
        refine congrArg₂ (fun (c : ℂˣ) (v : ⨂[ℂ] _ : Fin N, ℂ) => (c : ℂ) • v) ?_ ?_
        · refine (Finset.prod_congr rfl fun a _ => ?_)
          rw [hd, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)]
        · have hκ : ∀ w, κ w = w • PiTensorProduct.tprod ℂ (fun _ : Fin N => (1 : ℂ)) := fun w => by
            apply κ.symm.injective
            simp [κ]
          rw [hκ, hκ, map_smul, piTensor_tprod, ofChar_apply, torusChar_apply]
          have : (fun i => detRep (Fin 1) (χ i) (leviProj k e p i) 1) =
              fun i => (χ i (GeneralLinearGroup.det (leviProj k e p i)) : ℂ) • (1 : ℂ) := by
            funext i
            simp [detRep]
          rw [this, MultilinearMap.map_smul_univ, smul_smul, mul_comm, Units.coe_prod]
          simp only [hd]
          rfl⟩
  refine .of_injective ⟨Ψ, fun g => rfl⟩ fun f f' h => ?_
  exact Subtype.ext (Subtype.ext (funext fun x =>
    κ.injective (congrFun (congrArg (fun φ => φ.1.1) h) x)))

end GlobalTheory.PrinProd
end
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.isOpenEmbedding_finiteAdeleOfSPartAndIntegralPart : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), IsOpenEmbedding (jS F S) := by
  first | exact @GlobalTheory.ModuLR.isOpenEmbedding_jS | exact GlobalTheory.ModuLR.isOpenEmbedding_jS | (intros; apply GlobalTheory.ModuLR.isOpenEmbedding_jS <;> assumption)
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.addEquivAddHaarChar_prodCongr : ∀ (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂), addEquivAddHaarChar (prodCE e₁ e₂) = addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂ := by
  first | exact @GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE | exact GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE | (intros; apply GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE <;> assumption)
end

section

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem splitClosed_etale (F P Ω n : Type) [Field F] [CommRing P] [Algebra F P] [Fintype n]
    [Algebra.Etale F P] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (h : Module.finrank F P = Fintype.card n) :
    Nonempty (Ω ⊗[F] P ≃ₐ[Ω] (n → Ω)) := by
  classical
  haveI : Module.Finite F P := Algebra.FormallyUnramified.finite_of_free F P
  haveI : IsArtinianRing (Ω ⊗[F] P) := isArtinian_of_tower Ω inferInstance
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[F] P)
  letI : Fintype (PrimeSpectrum (Ω ⊗[F] P)) := Fintype.ofFinite _
  have hc : Fintype.card (PrimeSpectrum (Ω ⊗[F] P)) = Fintype.card n := by
    have := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_baseChange, h, Module.finrank_fintype_fun_eq_card] at this
    exact this.symm
  exact ⟨e.trans (AlgEquiv.piCongrLeft' Ω (fun _ => Ω) (Fintype.equivOfCardEq hc))⟩

theorem splitClosed_quad {F E : Type} [Field F] [CharZero F] [CommRing E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsQuadInvol F E σ) (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] :
    ∃ φ : E ⊗[F] Ω ≃ₐ[F] Ω × Ω, (∀ ω : Ω, φ (1 ⊗ₜ ω) = (ω, ω)) ∧
      ∀ u, φ (Algebra.TensorProduct.map σ (AlgHom.id F Ω) u) = (φ u).swap := by
  haveI := h.etale
  haveI := quad_finite h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨e⟩ := splitClosed_etale F E Ω (Fin 2) (by simp [h.finrank_eq])
  let θ : E →ₐ[F] Ω := (((Pi.evalAlgHom Ω (fun _ : Fin 2 => Ω) 0).comp e.toAlgHom).restrictScalars F).comp
    Algebra.TensorProduct.includeRight
  obtain ⟨b, d, -, hb1, hd, hbb⟩ := quad_exists_basis h
  have hc : θ (b 1) ≠ 0 := by
    intro h0
    have := congrArg θ hbb
    rw [map_mul, h0, mul_zero, AlgHom.commutes] at this
    exact hd ((map_eq_zero _).1 this.symm)
  let f : Ω ⊗[F] E →ₐ[Ω] Ω × Ω :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω (Ω × Ω)) (θ.prod (θ.comp σ)) (fun _ _ => Commute.all _ _)
  have hf : ∀ ω x, f (ω ⊗ₜ x) = (ω * θ x, ω * θ (σ x)) := by
    intro ω x; simp [f, Algebra.ofId_apply]
  have hs : Function.Surjective f := by
    rintro ⟨x, y⟩
    refine ⟨((x + y) / 2) ⊗ₜ 1 + ((x - y) / (2 * θ (b 1))) ⊗ₜ b 1, ?_⟩
    rw [map_add (f := _), hf, hf, hb1, map_neg, map_one, map_one]
    ext <;> simp <;> field_simp <;> ring
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
      (by simp [h.finrank_eq])).2 hs
  refine ⟨(Algebra.TensorProduct.comm F E Ω).trans
    ((AlgEquiv.ofBijective f ⟨hi, hs⟩).restrictScalars F), fun ω => (hf ω 1).trans (by simp), fun u => ?_⟩
  induction u with
  | tmul a w =>
    change f (w ⊗ₜ σ a) = (f (w ⊗ₜ a)).swap
    rw [hf, hf, h.invol]; rfl
  | add a w ha hw => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hw, Prod.swap_add]

def splitClosedPair (F Ω n : Type) [Field F] [Field Ω] [Algebra F Ω] :
    ((n → Ω) × (n → Ω)) ≃ₐ[F] (n → Ω × Ω) where
  toFun x i := (x.1 i, x.2 i)
  invFun y := (fun i => (y i).1, fun i => (y i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem splitClosed : SplitClosed := by
  intro F E _ _ _ _ σ h P _ _ n _ hP ⟨b⟩ Ω _ _ _
  obtain ⟨e⟩ := splitClosed_etale F P Ω n (Module.finrank_eq_card_basis b)
  obtain ⟨g, hg1, hg⟩ := splitClosed_quad h Ω
  let e' : P ⊗[F] Ω ≃ₐ[F] (n → Ω) := (Algebra.TensorProduct.comm F P Ω).trans (e.restrictScalars F)
  have he' : ∀ ω : Ω, e' (1 ⊗ₜ ω) = fun _ => ω := fun ω => e.commutes ω
  let φ : P ⊗[F] (E ⊗[F] Ω) ≃ₐ[F] (n → Ω × Ω) :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[F] P) g).trans
      (Algebra.TensorProduct.prodRight F F P Ω Ω)).trans
      ((AlgEquiv.prodCongr e' e').trans (splitClosedPair F Ω n))
  have hφ : ∀ p x i, φ (p ⊗ₜ x) i = (e' (p ⊗ₜ (g x).1) i, e' (p ⊗ₜ (g x).2) i) := by
    intro p x i; rfl
  refine ⟨φ, fun ω => funext fun i => by rw [hφ, hg1, he'], fun u i => ?_⟩
  induction u with
  | tmul p x => rw [tConj3, Algebra.TensorProduct.map_tmul, hφ, hφ, hg]; rfl
  | add a w ha hw => rw [map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, ha, hw, Prod.swap_add]

end GlobalTheory.RegSS
end
end

section

open GlobalTheory.RegSS

namespace GlobalTheory.RegSS

theorem eq_zero_of_trace_mul_eq_zero {F L : Type} [Field F] [CharZero F] [CommRing L]
    [Algebra F L] [Module.Finite F L] [IsReduced L] (x : L)
    (hx : ∀ y : L, Algebra.trace F L (x * y) = 0) : x = 0 := by
  have : IsArtinianRing L := IsArtinianRing.of_finite F L
  have : IsSemisimpleRing L := IsArtinianRing.isSemisimpleRing_of_isReduced L

  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {x})
  have hem : e ∈ Ideal.span {x} := hI ▸ Ideal.mem_span_singleton_self e
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hem

  have htr : LinearMap.trace F L (Algebra.lmul F L e) = 0 := by
    rw [← Algebra.trace_apply, ← ha, mul_comm]
    exact hx a
  have hidem : IsIdempotentElem (Algebra.lmul F L e) := he.map (Algebra.lmul F L)
  have h0 : Algebra.lmul F L e = 0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem htr
  have he0 : e = 0 := by
    have := congrArg (fun f => f 1) h0
    simpa using this
  rw [he0] at hI
  exact Ideal.span_singleton_eq_bot.1 (hI.trans (Ideal.span_singleton_eq_bot.2 rfl))

end GlobalTheory.RegSS

namespace GlobalTheory.RegSS

theorem tracePerfect : TracePerfect := by
  unfold TracePerfect
  intro F E L _ _ _ _ _ _ _ _ _ _ _ _
  have : Module.Finite F L := Module.Finite.trans E L
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have inj : Function.Injective (Algebra.traceForm E L) := by
    intro x y hxy

    have h : ∀ z : L, Algebra.trace F L ((x - y) * z) = 0 := by
      intro z
      have hz := LinearMap.congr_fun hxy z
      rw [Algebra.traceForm_apply, Algebra.traceForm_apply] at hz
      rw [← Algebra.trace_trace (S := E), sub_mul, map_sub, hz, sub_self, map_zero]
    exact sub_eq_zero.1 (eq_zero_of_trace_mul_eq_zero (F := F) _ h)
  let b := Module.Free.chooseBasis E L
  let g : L →ₗ[E] L := b.toDualEquiv.symm.toLinearMap ∘ₗ Algebra.traceForm E L
  have ginj : Function.Injective g := b.toDualEquiv.symm.injective.comp inj
  refine ⟨inj, fun f => ?_⟩
  obtain ⟨x, hx⟩ := (IsArtinian.bijective_of_injective_endomorphism g ginj).2
    (b.toDualEquiv.symm f)
  exact ⟨x, b.toDualEquiv.symm.injective hx⟩

end GlobalTheory.RegSS
end

section

noncomputable section

open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem nonempty_algHom_algebraicClosure (F A : Type) [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] [Nontrivial A] : Nonempty (A →ₐ[F] AlgebraicClosure F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m).toLinearMap (Ideal.Quotient.mkₐ_surjective F m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F m)⟩

theorem exists_eq_tmul_add_tmul {F E P : Type} [Field F] [CommRing E] [Algebra F E] [CommRing P]
    [Algebra F P] (b : Module.Basis (Fin 2) F E) (x : P ⊗[F] (E ⊗[F] F)) :
    ∃ p q : P, x = p ⊗ₜ (b 0 ⊗ₜ (1 : F)) + q ⊗ₜ (b 1 ⊗ₜ (1 : F)) := by
  induction x with
  | tmul p y =>
    obtain ⟨e, rfl⟩ := (TensorProduct.rid F E).symm.surjective y
    refine ⟨b.repr e 0 • p, b.repr e 1 • p, ?_⟩
    have hs := b.sum_repr e
    rw [Fin.sum_univ_two] at hs
    rw [TensorProduct.rid_symm_apply, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul, hs]
  | add x y hx hy =>
    obtain ⟨p, q, rfl⟩ := hx
    obtain ⟨p', q', rfl⟩ := hy
    exact ⟨p + p', q + q', by simp only [TensorProduct.add_tmul]; abel⟩

theorem separatingPoints : SeparatingPoints := by
  intro F E _ _ _ _ σ hσ P _ _ _ k K _ _ ⟨e⟩
  haveI := quad_finite hσ
  haveI := quad_nontrivial hσ
  obtain ⟨b, d, hb0, hb1, hd, hbb⟩ := quad_exists_basis hσ
  let pr : ∀ i, P →ₐ[F] K i := fun i => (Pi.evalAlgHom F K i).comp e.toAlgHom
  have hpr : ∀ i p, pr i p = e p i := fun _ _ => rfl
  haveI : ∀ i, Module.Finite F (K i) := fun i =>
    Module.Finite.of_surjective (pr i).toLinearMap fun y => by
      obtain ⟨p, hp⟩ := e.surjective (Pi.single i y)
      exact ⟨p, by simp [hpr, hp]⟩
  let χ : ∀ i, K i ⊗[F] E →ₐ[F] AlgebraicClosure F := fun i =>
    (nonempty_algHom_algebraicClosure F (K i ⊗[F] E)).some
  let π : ∀ i, P ⊗[F] (E ⊗[F] F) →ₐ[F] K i ⊗[F] E := fun i =>
    Algebra.TensorProduct.map (pr i) (Algebra.TensorProduct.rid F F E).toAlgHom
  have hπ : ∀ i p (y : E), π i (p ⊗ₜ (y ⊗ₜ (1 : F))) = e p i ⊗ₜ y := fun i p y => by
    simp [π, hpr]
  have hc : ∀ (p : P) (y : E), tConj3 P σ F (p ⊗ₜ (y ⊗ₜ (1 : F))) = p ⊗ₜ (σ y ⊗ₜ (1 : F)) :=
    fun p y => by simp [tConj3]
  refine ⟨fun i => (χ i).comp (π i), fun x hx => ?_, fun i hi x hx => ?_⟩
  · obtain ⟨p, q, rfl⟩ := exists_eq_tmul_add_tmul b x
    have key : ∀ i, e p i = 0 ∧ e q i = 0 := fun i => by
      obtain ⟨h1, h2⟩ := hx i
      have hm : (e q i ⊗ₜ[F] b 1 : K i ⊗[F] E) = (e q i ⊗ₜ[F] 1) * (1 ⊗ₜ[F] b 1) := by simp
      simp only [AlgHom.comp_apply, map_add (f := _), hc, hπ, hb0, hb1, map_one, TensorProduct.tmul_neg,
        map_neg] at h1 h2
      rw [hm, map_mul] at h1 h2
      have hδ : χ i (1 ⊗ₜ[F] b 1) ≠ 0 := fun h0 => by
        have : χ i (1 ⊗ₜ[F] b 1) * χ i (1 ⊗ₜ[F] b 1) = algebraMap F _ d := by
          rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, hbb, mul_one,
            ← Algebra.TensorProduct.algebraMap_apply', AlgHom.commutes]
        rw [h0, zero_mul] at this
        exact hd ((map_eq_zero _).1 this.symm)
      have inj : ∀ y : K i, χ i (y ⊗ₜ[F] 1) = 0 → y = 0 := fun y hy =>
        (map_eq_zero ((χ i).comp Algebra.TensorProduct.includeLeft : K i →ₐ[F] _)).1 hy
      refine ⟨inj _ (by linear_combination (h1 + h2) / 2), inj _ ?_⟩
      exact (mul_eq_zero.1 (by linear_combination (h1 - h2) / 2)).resolve_right hδ
    have hp : p = 0 := e.injective (by rw [map_zero]; exact funext fun i => (key i).1)
    have hq : q = 0 := e.injective (by rw [map_zero]; exact funext fun i => (key i).2)
    simp [hp, hq]
  · have h0 : π i x = 0 := by
      by_contra h0
      obtain ⟨y, hy⟩ := hi.mul_inv_cancel h0
      have := congrArg (χ i) hy
      rw [map_mul, show χ i (π i x) = 0 from hx, zero_mul, map_one] at this
      exact zero_ne_one this
    have h1 : π i (tConj3 P σ F x) = tConj (K i) σ (π i x) := by
      obtain ⟨p, q, rfl⟩ := exists_eq_tmul_add_tmul b x
      simp only [map_add (f := _), hc, hπ, tConj, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [AlgHom.comp_apply, h1, h0, map_zero, map_zero]

end GlobalTheory.RegSS
end
end

section

open Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem fieldUnitBounded_of_packing (hP : NormOnePacking) (hT : TensorLattice) :
    FieldUnitBounded := by
  unfold FieldUnitBounded
  intro F B _ _ _ _ _ τ hB hτ

  obtain ⟨hTop, hLC, hT2, hSC, _hinj, hdisc, C, hC, hcov⟩ := hT F B
  let : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  have := hTop
  have := hLC
  have := hT2
  have := hSC

  have : Nontrivial B := ⟨hB.exists_pair_ne⟩
  have : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have : Infinite B := Infinite.of_injective (algebraMap F B) (algebraMap F B).injective
  have : NoncompactSpace (B ⊗[F] AdeleRing (𝓞 F) F) := by
    refine ⟨fun hU => ?_⟩
    have hfin := hdisc Set.univ hU
    simp only [Set.mem_univ, Set.ofPred_true] at hfin
    exact Set.infinite_univ hfin

  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable B := (Module.finBasis F B).equivFun.injective.countable

  let ι := inclE (F := F) (E := B) (AdeleRing (𝓞 F) F)
  let Λ : AddSubgroup (B ⊗[F] AdeleRing (𝓞 F) F) := ι.toAddMonoidHom.range
  have hΛ : Countable Λ := by
    refine Function.Surjective.countable (f := fun b : B => (⟨ι b, b, rfl⟩ : Λ)) ?_
    rintro ⟨y, b, rfl⟩
    exact ⟨b, rfl⟩
  have hcoc : ∃ C' : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact C' ∧
      ∀ x, ∃ l ∈ Λ, x - l ∈ C' := by
    refine ⟨C, hC, fun x => ?_⟩
    obtain ⟨β, hβ⟩ := hcov x
    exact ⟨ι β, ⟨β, rfl⟩, hβ⟩

  obtain ⟨D, hD, hDu⟩ := hP (B ⊗[F] AdeleRing (𝓞 F) F) (sigR τ (AdeleRing (𝓞 F) F))
    (continuous_sigR τ (AdeleRing (𝓞 F) F)) (sigR_sigR hτ (AdeleRing (𝓞 F) F)) Λ hΛ hcoc
  refine ⟨D, hD, fun u hu => ?_⟩
  obtain ⟨β, ⟨b, rfl⟩, hβ0, huβ⟩ := hDu u hu

  have hb : b ≠ 0 := by
    rintro rfl
    exact hβ0 (map_zero ι)
  obtain ⟨c, hc⟩ := hB.mul_inv_cancel hb
  exact ⟨b, ⟨⟨b, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩, huβ⟩

end GlobalTheory.RegSS
end
