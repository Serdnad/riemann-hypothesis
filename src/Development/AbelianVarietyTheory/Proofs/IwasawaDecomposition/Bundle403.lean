module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle309
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Formalism.LocalToGlobal.HermitianForms.Bundle008
public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle390
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ClsBij

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem ratAd_mem_ratPts (hc : CMData F E) (γ : UF E n) :
    ratAd F γ ∈ ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) := by
  refine ⟨ufGL E n γ, ?_, rfl⟩
  show cT _ _ * 1 * _ = 1
  rw [mul_one]
  exact GlobalTheory.Mem.Col2.StepOk.ufGL_conjTranspose_mul γ

theorem exists_ratAd_eq (hc : CMData F E) {g : GL (Fin n) (AfE F E)}
    (hg : g ∈ ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ γ : UF E n, ratAd F γ = g := by
  obtain ⟨r, hr, rfl⟩ := hg
  refine ⟨ratEquiv hc n ⟨r, hr⟩, ?_⟩
  show Formalism.UG.bc _ (ufGL E n _) = _
  rw [GlobalTheory.Mem.Col2.RatMove.ufGL_eq hc, MulEquiv.symm_apply_apply]

end SlopeTestRemainingChoices

theorem classes_bijective : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (C : Type) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (s : C → DecoF E n ST SG Q) (U : Subgroup (GL (Fin n) (AfE F E))) (k' : GL (Fin n) (AfE F E)) (y : C → UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)), U ≤ UAd hc n → k' ∈ UAd hc n → (∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * k') p → IsPtOf hc (g * x * k') p' → (x ∈ U ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p')) → (∀ g ∈ UAd hc n, ∃ x ∈ U, ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * x * k') p) → (∀ c, IsPtOf hc ((y c).1 * k') (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = p) → Function.Bijective (fun c => (Quotient.mk'' (y c) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) (U.subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))))) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q C Λ Θ s U k' y hU hk' hlev hdense hpt hinj hsurj
  constructor
  · intro c c' hcc
    obtain ⟨γ, hγ, u, hu, he⟩ := (@DoubleCoset.eq _ _ _ _ (y c) (y c')).1 hcc
    have he' : (y c').1 = γ.1 * (y c).1 * u.1 := by rw [he]; rfl
    obtain ⟨δ, hδ⟩ := exists_ratAd_eq hc (Subgroup.mem_subgroupOf.1 hγ)
    have h1 := GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q δ⁻¹ _ _ (hpt c')
    have e1 : ratAd F δ⁻¹ * ((y c').1 * k') = (y c).1 * u.1 * k' := by
      rw [he', ← hδ, ← GlobalTheory.Mem.Col2.TilX.ratAd_inv]
      group
    rw [e1] at h1
    obtain ⟨h, θ, hhθ⟩ := (hlev (y c).1 u.1 (s c) _ (hpt c) h1).1 (Subgroup.mem_subgroupOf.1 hu)
    refine hinj c c' δ h θ ?_
    have e2 : ((δ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) =
        ((δ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) := by
      simp
    rw [e2, mul_smul, hhθ, smul_smul]
    have e3 : ((δ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * ((δ⁻¹, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) = 1 := by
      simp
    rw [e3, one_smul]
  · intro q
    induction q using Quotient.inductionOn' with
    | h z =>
    obtain ⟨x, hx, p, hp⟩ := hdense z.1 z.2
    obtain ⟨c, γ, h, θ, hcp⟩ := hsurj p
    refine ⟨c, ?_⟩
    have h1 := GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q γ⁻¹ _ _ hp
    have e1 : ((γ⁻¹, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p =
        ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c := by
      rw [← hcp, smul_smul]
      congr 1
      simp
    rw [e1] at h1
    have e2 : ratAd F γ⁻¹ * (z.1 * x * k') = (y c).1 * ((y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x) * k' := by
      group
    rw [e2] at h1
    have hx' : (y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x ∈ U := (hlev (y c).1 _ (s c) _ (hpt c) h1).2 ⟨h, θ, rfl⟩
    let kk : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) :=
      ⟨(y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x * x⁻¹, hU (mul_mem hx' (inv_mem hx))⟩
    show DoubleCoset.mk _ _ (y c) = DoubleCoset.mk _ _ z
    refine (@DoubleCoset.eq _ _ _ _ (y c) z).2 ⟨z * kk⁻¹ * (y c)⁻¹, ?_, kk, Subgroup.mem_subgroupOf.2 (mul_mem hx' (inv_mem hx)), by group⟩
    rw [Subgroup.mem_subgroupOf]
    have e4 : ((z * kk⁻¹ * (y c)⁻¹ : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (AfE F E))
        = ratAd F γ := by
      show z.1 * ((y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x * x⁻¹)⁻¹ * (y c).1⁻¹ = _
      rw [← GlobalTheory.Mem.Col2.TilX.ratAd_inv]
      group
    rw [e4]
    exact ratAd_mem_ratPts hc γ

end GlobalTheory.Mem.Col2.ClsBij
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.RowPar

section Sat
open Formalism.UG GlobalTheory.SatInd

theorem satAtS_indep {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ (GAf L n → W)) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv Dv' : InertDatum L n v w) (α : Fin (n / 2) → ℂ) (hs : NG.SatAtS S Dv α) : NG.SatAtS S Dv' α := by
  obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hs
  refine ⟨f, hfS, hf0, U, hU, hUv, fun h' hh' => ?_⟩
  have hm : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  rw [GlobalTheory.T.inertHeckeOperator_indep_of_inertDatum L n v w Dv Dv' U _ h' hh'.1 f,
    hH _ (GlobalTheory.T.heckeAlgebra_comp_unitaryGroupAntidiagTransport_mem (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') n h' hh'),
    GlobalTheory.T.unitarySatake_invariant_antidiagTransport (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ n (n / 2) h' hh'.1
      (GlobalTheory.T.unitaryTorus_unipotent_coset_transport_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ _ n (n / 2)
        Dv.unram Dv'.unram hm)]

end Sat

section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands

theorem ringHom_ext_adicCompletion {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {R : Type} [Ring R]
    [TopologicalSpace R] [T2Space R] (f g : v.adicCompletion K →+* R) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ y : K, f (algebraMap K _ y) = g (algebraMap K _ y)) : f = g :=
  DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap K v).equalizer hf hg (funext h))

theorem splitEmb_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (si si' : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (i i' : v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L) (hi : Continuous i) (hi' : Continuous i')
    (hix : ∀ x, i (si x) = algebraMap L _ x) (hix' : ∀ x, i' (si' x) = algebraMap L _ x) : si' = si ∧ i' = i := by
  have e : (i' : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) = i := by
    refine ringHom_ext_adicCompletion v _ _ hi' hi fun y => ?_
    have h1 := hix (algebraMap _ L y)
    have h2 := hix' (algebraMap _ L y)
    rw [AlgHom.commutes] at h1 h2
    exact h2.trans h1.symm
  have e' : i' = i := RingEquiv.ext fun x => congrArg (fun f : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L => f x) e
  refine ⟨AlgHom.ext fun x => i.injective ?_, e'⟩
  rw [hix, ← hix' x, e']

theorem splitPlace_eq_of_isLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (S S' : Submodule ℂ (GAf L n → W)) (s s' : SplitPlace L) (h : s'.w = s.w)
    (τ : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (τ' : IrrRep (GL (Fin n) (s'.w.adicCompletion L)))
    (hτ : IsLocS S s τ) (hτ' : IsLocS S' s' τ') : s' = s := by
  obtain ⟨i, -, hi, hix, -⟩ := hτ
  obtain ⟨i', -, hi', hix', -⟩ := hτ'
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  have key : ∀ (w : HeightOneSpectrum (𝓞 L)) (hw : s'.w = w)
      (j : s'.v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L), Continuous j →
      (∀ x, j (s'.i x) = algebraMap L _ x) → s' = s := by
    intro w hw j hj hjx
    rw [h] at hw
    subst hw
    obtain ⟨v, si⟩ := s
    obtain ⟨v', si'⟩ := s'
    dsimp only at hv
    subst hv
    obtain rfl := (splitEmb_eq _ _ si si' i j hi hj hix hjx).1
    rfl
  exact key _ rfl i' hi' hix'

theorem cl_eq_of_isLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : NG.FinTyp L n) (s : SplitPlace L)
    (τ τ' : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hτ : IsLocS π.S s τ) (hτ' : IsLocS π.S s τ') : τ.cl = τ'.cl := by
  obtain ⟨i, T, hi, hix, hTi, hTS, hTe⟩ := hτ
  obtain ⟨i', T', hi', hix', hTi', hTS', hTe'⟩ := hτ'
  obtain rfl := (splitEmb_eq s.v s.w s.i s.i i' i hi' hi hix' hix).2
  obtain ⟨hdec, hcom, huniq⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose sec hsec using fun A => (huniq A).exists
  have sec_eq : ∀ x : GAf L n, TrivOutside {s.v} x → sec (s.loc n x) = x := fun x hx =>
    (huniq _).unique (hsec _) ⟨hx, rfl⟩
  have triv_mul : ∀ x y : GAf L n, TrivOutside {s.v} x → TrivOutside {s.v} y → TrivOutside {s.v} (x * y) := by
    intro x y hx hy v hv
    have h1 := hx v hv
    have h2 := hy v hv
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [Matrix.map_mul, h1, h2, one_mul]
  have triv_one : TrivOutside {s.v} (1 : GAf L n) := by
    intro v _
    simp [Matrix.map_one]
  let sH : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := sec
      map_one' := (huniq 1).unique (hsec 1) ⟨triv_one, map_one _⟩
      map_mul' := fun A B => (huniq (A * B)).unique (hsec (A * B))
        ⟨triv_mul _ _ (hsec A).1 (hsec B).1, by rw [map_mul, (hsec A).2, (hsec B).2]⟩ }
  let ρ : Representation ℂ (GAf L n) π.S :=
    { toFun := fun g => (NG.rt L n g).restrict (fun f hf => π.stable g f hf)
      map_one' := LinearMap.ext fun f => Subtype.ext (funext fun x => by simp [NG.rt])
      map_mul' := fun g h => LinearMap.ext fun f => Subtype.ext (funext fun x => by simp [NG.rt, mul_assoc]) }
  have hρ : ρ.IsIrreducible := by
    refine (GlobalTheory.CuspRep.isIrreducible_iff ρ).2 ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne, fun U hU => ?_⟩
    have hst : ∀ h, ∀ f ∈ U.map π.S.subtype, NG.rt L n h f ∈ U.map π.S.subtype := by
      rintro h _ ⟨u, hu, rfl⟩
      exact ⟨ρ h u, hU h u hu, rfl⟩
    rcases π.irr _ (Submodule.map_subtype_le _ _) hst with h0 | h1
    · left
      exact Submodule.map_injective_of_injective π.S.injective_subtype (h0.trans (Submodule.map_bot _).symm)
    · right
      refine Submodule.map_injective_of_injective π.S.injective_subtype ?_
      rw [h1, Submodule.map_subtype_top]
  let e : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map i.toRingHom
  have he : Function.Surjective e := fun B =>
    ⟨Matrix.GeneralLinearGroup.map i.symm.toRingHom B, Units.ext (Matrix.ext fun a b => by simp [e])⟩
  have hnt : ∀ τ₀ : IrrRep (GL (Fin n) (s.w.adicCompletion L)), Nontrivial τ₀.V := fun τ₀ =>
    ((GlobalTheory.CuspRep.isIrreducible_iff τ₀.ρ).1 τ₀.irr).1
  have key : ∀ (τ₀ : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (T₀ : τ₀.V →ₗ[ℂ] (GAf L n → ℂ)),
      Function.Injective T₀ → (∀ a, T₀ a ∈ π.S) →
      (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a,
        T₀ (τ₀.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T₀ a)) →
      ∃ f : Representation.IntertwiningMap (τ₀.ρ.comp e) (ρ.comp sH), f ≠ 0 := by
    intro τ₀ T₀ hT₀ hS₀ he₀
    refine ⟨⟨LinearMap.codRestrict π.S T₀ hS₀, fun A => LinearMap.ext fun a => Subtype.ext ?_⟩, fun h0 => ?_⟩
    · have h1 := he₀ (sec A) (hsec A).1 a
      rw [(hsec A).2] at h1
      exact h1
    · haveI := hnt τ₀
      obtain ⟨a, ha⟩ := exists_ne (0 : τ₀.V)
      refine ha (hT₀ ?_)
      have h2 := congrArg (fun f : Representation.IntertwiningMap (τ₀.ρ.comp e) (ρ.comp sH) => (f a : GAf L n → ℂ)) h0
      simpa using h2
  obtain ⟨f, hf⟩ := @key τ T hTi hTS hTe
  obtain ⟨f', hf'⟩ := key τ' T' hTi' hTS' hTe'
  have hcomm : ∀ g, ∃ u, ∀ y, Commute ((sH u)⁻¹ * g) (sH y) := by
    intro g
    obtain ⟨x, y, hx, hy, rfl⟩ := hdec g
    refine ⟨s.loc n x, fun B => ?_⟩
    rw [show sH (s.loc n x) = x from sec_eq x hx, inv_mul_cancel_left]
    exact (hcom _ _ (hsec B).1 hy).symm
  obtain ⟨φ⟩ := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ ρ sH (τ.ρ.comp e) (τ'.ρ.comp e) hρ
    (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ.irr e he) (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ'.irr e he)
    hcomm f hf).2 f' hf'
  refine IrrRep.cl_eq_iff.2 ⟨Representation.Equiv.mk φ.toLinearEquiv fun B => ?_⟩
  obtain ⟨A, rfl⟩ := he B
  exact φ.isIntertwining' A

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)

def LocAt (σ : D.what₂.FT) (w : PlE D.host) : Type 1 :=
  {p : (s : SplitPlace D.host.E) × IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) //
    p.1.w = w ∧ IsLocS (rep σ).S p.1 p.2}

def unrW : RowWD D := by
  let m : Multiset ℂ := Multiset.replicate D.R.r 1
  have hm : (0 : ℂ) ∉ m := fun h => zero_ne_one (Multiset.eq_of_mem_replicate h)
  exact
    { par := fun _ w => GlobalTheory.WeilDeligne.WD.lpUnr (D.nd.plOm.2 w) m
      sat := fun _ _ => m
      dim := fun _ w =>
        (GlobalTheory.WeilDeligne.WD.lpUnr_spec (h := D.nd.plOm.2 w) m hm).2.2.trans
          (Multiset.card_replicate _ _)
      tame := fun _ k v =>
        GlobalTheory.WeilDeligne.WD.tame_of_unr
          (GlobalTheory.WeilDeligne.WD.lpUnr_spec (h := D.nd.plOm.2 (D.naut.plGw k v)) m hm).1 }

end Loc

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

def satOf (S : Submodule ℂ (GAf L n → W)) (w : HeightOneSpectrum (𝓞 L)) : Multiset ℂ := by
  classical
  exact if h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAtS S Dv α then Finset.univ.val.map h.choose_spec.choose_spec.choose else 0

theorem satAtS_transfer (S : Submodule ℂ (GAf L n → W)) {w : HeightOneSpectrum (𝓞 L)}
    (v0 v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv0 : InertDatum L n v0 w) (Dv : InertDatum L n v w)
    (hv : v0 = v) (α : Fin (n / 2) → ℂ) (hs : NG.SatAtS S Dv0 α) : NG.SatAtS S Dv α := by
  subst hv
  exact satAtS_indep S Dv0 Dv α hs

theorem satOf_spec (S : Submodule ℂ (GAf L n → W)) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (hO : NG.OverPl w v) (Dv : InertDatum L n v w) (hα : ∃ α, NG.SatAtS S Dv α) :
    ∃ α, NG.SatAtS S Dv α ∧ satOf S w = Finset.univ.val.map α := by
  classical
  obtain ⟨α, hα⟩ := hα
  have h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAtS S Dv α := ⟨v, Dv, α, hO, hα⟩
  have hsp := h.choose_spec.choose_spec.choose_spec
  refine ⟨h.choose_spec.choose_spec.choose, satAtS_transfer S _ v _ Dv
    (HeightOneSpectrum.ext (hsp.1.symm.trans hO)) _ hsp.2, ?_⟩
  unfold satOf
  rw [dite_eq_left h]

end GlobalTheory.RowPar
end
end

section

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  NumberField IsDedekindDomain Polynomial Module Module.End

section Gen
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem heckeEig_mem_iff_gens (N : NData R H what₂) (i : N.Loc) (x : N.X i)
    (y : TensorProduct (N.O i) (FractionRing (N.O i)) (N.Mt i)) :
    y ∈ heckeEig (N.T i) (N.act i) x ↔ ∀ v k, SplitOut N i v → 1 ≤ k → k ≤ R.nV →
      ((N.act i (N.hT i v k)).baseChange (FractionRing (N.O i))) y =
        algebraMap (N.O i) (FractionRing (N.O i)) ((N.hT i v k : N.X i → N.O i) x) • y := by
  constructor
  · intro hy v k _ _ _
    exact mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hy (N.hT i v k))
  · intro hy
    refine (Submodule.mem_iInf _).2 fun f => mem_eigenspace_iff.2 ?_
    obtain ⟨f, hf⟩ := f
    have hf' := hf
    rw [← N.T_gen i] at hf'
    suffices key : ∀ g (hg' : g ∈ Algebra.adjoin (N.O i) {g : N.X i → N.O i | ∃ v k, IsSplitPl H v ∧
        v ∉ placesOver H.E (N.l i) ∧ v ∉ N.S i ∧ v ∉ N.Q i ∧ 1 ≤ k ∧ k ≤ R.nV ∧
        g = (N.hT i v k : N.X i → N.O i)}), ∀ hg : g ∈ N.T i,
        ((N.act i ⟨g, hg⟩).baseChange (FractionRing (N.O i))) y =
          algebraMap (N.O i) (FractionRing (N.O i)) (g x) • y from key f hf' hf
    intro g hg'
    induction hg' using Algebra.adjoin_induction with
    | mem g hg0 =>
      intro hg
      obtain ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩ := hg0
      exact hy v k ⟨h1, h2, h3, h4⟩ h5 h6
    | algebraMap r =>
      intro hg
      have e : (⟨algebraMap (N.O i) (N.X i → N.O i) r, hg⟩ : N.T i) =
          algebraMap (N.O i) (N.T i) r := rfl
      rw [e, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul,
        LinearMap.baseChange_one]
      simp [algebraMap_smul]
    | add g g' hg1 hg2 ih1 ih2 =>
      intro hg
      have m1 : g ∈ N.T i := N.T_gen i ▸ hg1
      have m2 : g' ∈ N.T i := N.T_gen i ▸ hg2
      have e : (⟨g + g', hg⟩ : N.T i) = ⟨g, m1⟩ + ⟨g', m2⟩ := rfl
      rw [e, map_add (f := _), LinearMap.baseChange_add, LinearMap.add_apply, ih1 m1, ih2 m2, Pi.add_apply, map_add (f := _),
        add_smul]
    | mul g g' hg1 hg2 ih1 ih2 =>
      intro hg
      have m1 : g ∈ N.T i := N.T_gen i ▸ hg1
      have m2 : g' ∈ N.T i := N.T_gen i ▸ hg2
      have e : (⟨g * g', hg⟩ : N.T i) = ⟨g, m1⟩ * ⟨g', m2⟩ := rfl
      rw [e, map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, ih2 m2, LinearMap.map_smul, ih1 m1,
        smul_smul, Pi.mul_apply, map_mul, mul_comm]

end Gen

section Spec
variable {D : D7} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
  {X : LocNd (lay0 D)} {T : LocTw X}

theorem genAt_iff_splitOut (Sp : NdSpec Pl M C big X T) {j : ℕ} {w : D.what₂.places.Pl} {i : X.nd.Loc}
    (h : i ∈ X.nd.locs j w) (v : PlE D.host) (k : ℕ) :
    (SplitOut X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) ↔ GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by
  obtain ⟨-, h2⟩ := (X.nd.locs_mem j w i).1 h
  have hl : X.nd.l i = D.what₂.places.resChar w := by rw [← X.nd.w_l i, h2]
  have hS : v ∈ X.nd.S i ↔ v ∈ placesS D (D.what₂.places.resChar w) := by
    rw [X.nd.S_def, hl]; rfl
  unfold SplitOut GenAt
  rw [hS, ← Sp.Q_eq j w i h, hl]
  tauto

theorem mult_eq_finrank_jointEig (D : D7) (Pl : PlSide D) (M : MtFam D) (C : NChoice D)
    (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (j : ℕ)
    (w : D.what₂.places.Pl) (i : X.nd.Loc) (h : i ∈ X.nd.locs j w) (x : X.nd.X i) :
    X.nd.mult i x = Module.finrank (FractionRing (Sp.B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ)
      (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) := by
  set Fam := (⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) with hFam_def
  have hFam : ∀ e, e ∈ Fam ↔ ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      Sp.B.hK j w v k e = algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)) • e := by
    intro e
    simp only [Fam, Submodule.mem_iInf, mem_eigenspace_iff]
  have hval : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)) =
      NCov.pt (Sp.ptX j w i h x).1 ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := by
    intro v k hvk
    simp only [NCov.pt]
    rw [Sp.ptX_hT j w i h x v k hvk]
  have hE : ∀ e, e ∈ Fam ↔ e ∈ NCov.E (Formalism.L2.heckeAlg Sp.B j w) (Sp.ptX j w i h x).1 := by
    intro e
    rw [hFam, NCov.mem_E_iff]
    constructor
    · rintro hy _ ⟨v, k, hvk, rfl⟩
      rw [← hval v k hvk]
      exact hy v k hvk
    · intro hy v k hvk
      rw [hval v k hvk]
      exact hy _ ⟨v, k, hvk, rfl⟩
  have hpsi : ∀ y, y ∈ heckeEig (X.nd.T i) (X.nd.act i) x ↔ Sp.Psi j w i h y ∈ Fam := by
    intro y
    rw [heckeEig_mem_iff_gens, hFam]
    constructor
    · intro hy v k hvk
      obtain ⟨hso, hk1, hk2⟩ := (genAt_iff_splitOut Sp h v k).2 hvk
      have e := congrArg (Sp.Psi j w i h) (hy v k hso hk1 hk2)
      rw [Sp.act_hK j w i h v k hvk, LinearMap.map_smulₛₗ] at e
      rw [e]
      congr 1
      exact Sp.phK_alg j w i h _
    · intro hy v k hso hk1 hk2
      have hvk := (genAt_iff_splitOut Sp h v k).1 ⟨hso, hk1, hk2⟩
      apply Sp.Psi_inj j w i h
      rw [Sp.act_hK j w i h v k hvk, LinearMap.map_smulₛₗ, hy v k hvk]
      congr 1
      exact (Sp.phK_alg j w i h _).symm
  let f : ↥(heckeEig (X.nd.T i) (X.nd.act i) x) →ₛₗ[(Sp.phK j w i h).toRingHom] Sp.B.V j w :=
    (Sp.Psi j w i h).comp (heckeEig (X.nd.T i) (X.nd.act i) x).subtype
  change Module.finrank _ ↥(heckeEig (X.nd.T i) (X.nd.act i) x) = _
  refine finrank_eq_of_semilinear (Sp.phK j w i h) f Fam ?_ ?_
  · intro a b hab
    exact Subtype.ext (Sp.Psi_inj j w i h hab)
  · intro e
    constructor
    · intro he
      have hp : e ∈ NCov.part (Formalism.L2.heckeAlg Sp.B j w) (Sp.mx j w i) := by
        have := NCov.E_le_part (Formalism.L2.heckeAlg Sp.B j w) (Sp.ptX j w i h x).1 ((hE e).1 he)
        rwa [(Sp.ptX j w i h x).2.1] at this
      obtain ⟨z, rfl⟩ := (Sp.Psi_range j w i h e).1 hp
      exact ⟨⟨z, (hpsi z).2 he⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact (hpsi z).1 hz

end Spec

end GlobalTheory.HeightCounting
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tuple_integralForms_row_place_by_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ w, Formalism.L2.Forms.okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T w → ∀ x : (I.fm l u a).ptLat.V, x ∈ (I.fm l u a).SP w ↔ ∀ (c : (I.fm l u a).clsP) (Bm : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (I.rec7 l Z).host.E), IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (K.lat c : Set _) Bm → ∃ Pc ∈ IntSpan (I.rec7 l Z) w (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a ((I.fm l u a).ptEmb x) c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (I.rec7 l Z).host.E).1) Pc := by
  first | exact @GlobalTheory.Mem.Col2.TC.tw_lat_at | exact GlobalTheory.Mem.Col2.TC.tw_lat_at | (intros; apply GlobalTheory.Mem.Col2.TC.tw_lat_at <;> assumption)
end
