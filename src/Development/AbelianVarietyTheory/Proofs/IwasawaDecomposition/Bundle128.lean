module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle124
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle004
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitEmb
open GlobalTheory.SplitLift

section General
variable {n : ℕ} {K : Type*} (A : Type*) [CommRing K] [CommRing A]

def triMat (M : GL (Fin n) K) : Matrix (Fin n) (Fin n) (K × K × A) :=
  fun i j => ((M : Matrix (Fin n) (Fin n) K) i j, ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j i,
    (1 : Matrix (Fin n) (Fin n) A) i j)

theorem triMat_one : triMat A (1 : GL (Fin n) K) = 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [triMat, inv_one, Units.val_one, Matrix.one_apply, eq_comm (a := j)]
  split_ifs <;> rfl

theorem triMat_mul (M N : GL (Fin n) K) : triMat A (M * N) = triMat A M * triMat A N := by
  symm
  apply matrix_prod_ext
  · exact Matrix.map_mul (L := triMat A M) (M := triMat A N) (f := RingHom.fst K (K × A))
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.fst K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    change ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose *
      ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose =
      (((M * N)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.snd K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    exact Matrix.mul_one (1 : Matrix (Fin n) (Fin n) A)

end General

theorem exists_hom_trivOutside_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L),
    ∃ e : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) →* GAf L n,
      (∀ g, TrivOutside {s.v} (e g)) ∧ ∀ g, s.loc n (e g) = g := by
  intro L _ _ _ n s
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  set δ : L := y - IsCMField.complexConj L y with hδdef
  have hδ : IsCMField.complexConj L δ = -δ := by
    rw [hδdef, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hfix : IsCMField.complexConj L (δ * δ) = δ * δ := by rw [map_mul, hδ]; ring
  let d : maximalRealSubfield L := ⟨δ * δ, (IsCMField.complexConj_eq_self_iff L _).1 hfix⟩
  have hd : δ * δ = algebraMap (maximalRealSubfield L) L d := rfl
  have hr : s.i δ ≠ 0 := (map_ne_zero _).2 hδ0
  let X : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) → Matrix (Fin n) (Fin n) (AL L) :=
    fun M => (triMat (AL L) M).map (θ s δ d hd hr)
  have hX1 : X 1 = 1 := by
    show (triMat (AL L) 1).map (θ s δ d hd hr) = 1
    rw [triMat_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXm : ∀ M N, X (M * N) = X M * X N := fun M N => by
    show (triMat (AL L) (M * N)).map (θ s δ d hd hr) = _
    rw [triMat_mul, Matrix.map_mul]
  have hconj : ∀ M, conjT (conjAL L) (X M) = X M⁻¹ := fun M => by
    refine Matrix.ext fun i j => ?_
    simp only [conjT, X, Matrix.transpose_apply, Matrix.map_apply]
    rw [conj_θ s δ d hd hr hδ]
    congr 1
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [triMat, Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have hX : ∀ M, X M * conjT (conjAL L) (X M) = 1 := fun M => by
    rw [hconj, ← hXm, mul_inv_cancel, hX1]
  let e : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := fun M => ⟨⟨X M, conjT (conjAL L) (X M), hX M, mul_eq_one_comm.mp (hX M)⟩, hX M⟩
      map_one' := Subtype.ext (Units.ext hX1)
      map_mul' := fun M N => Subtype.ext (Units.ext (hXm M N)) }
  refine ⟨e, fun M w hw => ?_, fun M => ?_⟩
  · have hw' : w ≠ s.v := hw
    refine Matrix.ext fun i j => ?_
    change compAt L w (θ s δ d hd hr (triMat (AL L) M i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [compAt_θ s δ d hd hr _ hw']
    simp only [triMat, Matrix.one_apply]
    split_ifs <;> simp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change s.proj (θ s δ d hd hr (triMat (AL L) M i j)) = _
    rw [proj_θ]
    rfl

end GlobalTheory.SplitEmb
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem image_kerP_pow_separated : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (a : Per.Ainf l), (∀ k : ℕ, ∃ b : Per.Ainf l, algebraMap (Per.Ainf l) (Per.AinfP l) (a - ((l : ℕ) : Per.Ainf l) ^ k * b) ∈ Per.kerP l ^ n) → algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ n := by
  intro l _ n a h
  obtain ⟨e, he⟩ : ∃ e : Per.Fl l, IsEps e := Model.exists_isEps l
  obtain ⟨-, -, -, -, -, hinj, hk⟩ := thetaP_facts l
  obtain ⟨h1, h2⟩ := GlobalTheory.T.ainf_quot_fontaineXi_pow_torsionFree_separated l e he n
  have h3 : ∀ (j : ℕ) (c : Per.Ainf l), xi e ^ n ∣ ((l : ℕ) : Per.Ainf l) ^ j * c → xi e ^ n ∣ c := by
    intro j
    induction j with
    | zero => intro c hc; simpa using hc
    | succ j ih =>
      intro c hc
      refine h1 c (ih _ ?_)
      rwa [← mul_assoc, ← pow_succ]
  have key : ∀ c : Per.Ainf l, algebraMap (Per.Ainf l) (Per.AinfP l) c ∈ Per.kerP l ^ n ↔
      xi e ^ n ∣ c := by
    intro c
    rw [hk e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
    refine ⟨fun ⟨y, hy⟩ => ?_, fun hc => map_dvd _ hc⟩
    obtain ⟨j, d, hd⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    refine h3 j c ⟨d, hinj ?_⟩
    rw [map_mul, map_mul, ← hd, hy, map_pow, map_pow]
    ring
  refine (key a).2 (h2 a fun k => ?_)
  obtain ⟨b, hb⟩ := h k
  exact ⟨b, (key _).1 hb⟩

end GlobalTheory.MemLoc
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatInd

theorem satAt_indep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n), π.Iso π' → ∀ v w, NG.OverPl w v → ∀ (Dv Dv' : InertDatum L n v w) α, NG.SatAt π Dv α → NG.SatAt π' Dv' α := by
  intro L _ _ _ n π π' hiso v w _ Dv Dv' α hsat
  have h1 : NG.SatAt π Dv' α := by
    obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hsat
    refine ⟨f, hfS, hf0, U, hU, hUv, fun h' hh' => ?_⟩
    have hm : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    rw [GlobalTheory.T.inertHeckeOperator_indep_of_inertDatum L n v w Dv Dv' U _ h' hh'.1 f,
      hH _ (GlobalTheory.T.heckeAlgebra_comp_unitaryGroupAntidiagTransport_mem (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') n h' hh'),
      GlobalTheory.T.unitarySatake_invariant_antidiagTransport (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ n (n / 2) h' hh'.1
        (GlobalTheory.T.unitaryTorus_unipotent_coset_transport_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ _ n (n / 2)
          Dv.unram Dv'.unram hm)]
  exact GlobalTheory.T.inertSatakeParameters_eq_of_iso L n π π' hiso v w Dv' α
    (GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv' (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv'.ϖ Dv'.σw _ n Dv'.unram) (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv')) h1

end GlobalTheory.SatInd
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SphNonSplit

theorem not_split_of_overPl (D : D7) {w w' : PlE D.host} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (hw : NG.OverPl w v) (hw' : NG.OverPl w' v) (hs : ¬ IsSplitPl D.host w) : ¬ IsSplitPl D.host w' := by
  intro hs'
  have hu : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w =
      HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w' :=
    HeightOneSpectrum.ext (hw.trans hw'.symm)
  have hr : Module.finrank (maximalRealSubfield D.host.E) D.host.E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj D.host.E) hr
      (IsCMField.complexConj_ne_one D.host.E) w' w).1 hu with h | h
  · exact hs (h ▸ hs')
  · have hc : (IsCMField.complexConj D.host.E).toRingEquiv = D.host.conj.toRingEquiv := by
      refine RingEquiv.ext fun x => ?_
      apply D.host.φ₀.injective
      show D.host.φ₀ (IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
      rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    rw [hc] at h
    exact hs (GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl hs' ((GlobalTheory.Mem.Chr.conjPl_main.2.1 _ _ w' w).2 h))

theorem split_of_over_g (D : D7) (k : Fin 2) {w : PlE D.host} (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    IsSplitPl D.host w := by
  obtain ⟨u, h | h⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · rw [h]; exact GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u
  · exact GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u) h

theorem not_mem_bad (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C)
    (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v)
    (w0 : D.what₂.places.Pl) (j : Fin D.R.m) (w : PlE D.host) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hw : NG.OverPl w v) (hs : ¬ IsSplitPl D.host w) :
    v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w0) j) := by
  have hg : v ∉ gPl D := by
    rintro ⟨w', hw', k, hk⟩
    exact not_split_of_overPl D hw hw' hs (split_of_over_g D k hk)
  rintro (h | h)
  · exact hg h
  · rw [qPl_tup] at h
    obtain ⟨-, w', hw', hr⟩ := h
    apply not_split_of_overPl D hw hw' hs
    rw [tp.xi_tw] at hr
    by_contra hns
    apply hr
    have hpsi : (tp.psi w0).UnrAt w' := by
      obtain ⟨Q, hQ⟩ := tp.psi_gen w0
      exact (hQ.ram w').2 fun hq => hns (hQ.split w' hq)
    by_cases hl : D.what₂.places.resChar w0 = D.host.pde
    · have hd : cf.del'.UnrAt w' := cf.isDel'.unr w' fun hp => hns (hsp w' (Or.inr hp))
      intro x hx
      simp only [Host.CharFrame.delAt, hl, ↓reduceIte]
      change cf.del'.loc w' x * (tp.psi w0).loc w' x = 1
      rw [hd x hx, hpsi x hx, one_mul]
    · have hd : cf.del.UnrAt w' := cf.isDel.unr w' fun hp => hns (hsp w' (Or.inl hp))
      intro x hx
      simp only [Host.CharFrame.delAt, hl, ↓reduceIte]
      change cf.del.loc w' x * (tp.psi w0).loc w' x = 1
      rw [hd x hx, hpsi x hx, one_mul]

end GlobalTheory.SphNonSplit

namespace GlobalTheory.SphNonSplit

end GlobalTheory.SphNonSplit
end
end

section

open Formalism.L2.Forms GlobalTheory.IntegralityCompare

theorem _root_.GlobalTheory.T.automorphicFormFn_inv_iff_twistedSubstitution_mem : ∀ {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (S : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ)) {Yt : Type} (e : Yt ≃ Frames G) (f : Yt → ℂ),
    (∀ z, f z = fnOf G s 1 P0 (e z)) →
    ((∃ P ∈ S, ∀ z, f z = fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P (e z)) ↔
      twSub emb M s P0 ∈ S) := by
  first | exact @GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem | exact GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem | (intros; apply GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.Mem.R3.LiftLatBC

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

def bcF (φ : K →+* K') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0') (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K')
    (f : B.S.Forms) : B'.S.Forms :=
  B'.S.basis.equivFun.symm (C *ᵥ fun k => φ (B.S.basis.equivFun f k))

structure BlockBaseChangeAt (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (ℓ : Lvl K G) (ℓ' : Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K') : Prop where

  bij : Function.Bijective C.mulVec

  H : Cᴴ * B'.S.H * C = B.S.H.map φ

  act : ∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ

  nab : B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)))

  sub : B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K)))

  X : ∀ χ' : G' → K', χ' ∈ ℓ'.X ↔ ∃ χ ∈ ℓ.X, χ' = fun g => φ (χ (e.symm g))

  P : ℓ'.P = ℓ.P.map e.toMonoidHom

  ψ : ∀ h : ℓ.P, ((ℓ'.ψ ⟨e h, P ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : K'ˣ) : K') = φ (ℓ.ψ h : K)

section Cx

open Formalism.IndefR.Cx Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs}

theorem tC_cpt (cr : Crd A fc) (b : Bool) (j : Bs.J) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.tC cr b j t (cpt Bs.v0.embedding x) = X.θ' j t (X.jL j t (cr.toL X.zs b j t x)) := by
  have hx : x = ∑ k, x k • Pi.single k 1 := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp only [map_sum, map_smul, map_smulₛₗ, CxData.tC, lin, Fintype.linearCombination_apply, cpt]

end Cx

end GlobalTheory.Mem.R3.LiftLatBC

end
end

section

open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

namespace GlobalTheory

theorem exists_complexLinear_extension_of_traceIsometry : ∀ (K E : Type) [Field K] [Field E] [Algebra K E] (cj : E → E) (ι : Type) [Fintype ι] (φ : E →+* ℂ) (emb : ι → E →+* ℂ), (∀ y, φ (cj y) = starRingEnd ℂ (φ y)) → (∀ τ y, emb τ (cj y) = starRingEnd ℂ (emb τ y)) → (∀ τ (x : K), emb τ (algebraMap K E x) = φ (algebraMap K E x)) → (∀ y, ∑ τ, emb τ y = φ (algebraMap K E (Algebra.trace K E y))) → ∀ γ : IsoKG K E cj ι, ∃ gC : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ), ∀ x : Fin 4 → E, gC (fun w => emb w.2 (x w.1)) = fun w => φ (algebraMap K E (γ.g x w)) := by
  intro K E _ _ _ cj ι _ φ emb hφ hemb hK htr γ
  classical
  let b : Fin 4 × ι → Fin 4 → E := fun w => γ.g.symm (Pi.single w 1)
  let B : Matrix (Fin 4 × ι) (Fin 4 × ι) ℂ := fun v w => emb v.2 (b w v.1)
  have hB : Bᴴ * B = 1 := by
    ext w' w
    have h := congrArg φ (γ.isom (b w) (b w'))

    simp only [b, LinearEquiv.apply_symm_apply, map_sum, map_mul, hφ, ← htr, hemb] at h
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have h2 : ∑ a, ∑ τ, Bᴴ w' (a, τ) * B (a, τ) w
        = ∑ a, ∑ τ, emb τ (b w a) * starRingEnd ℂ (emb τ (b w' a)) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun τ _ => ?_
      rw [Matrix.conjTranspose_apply, mul_comm]
      rfl
    rw [h2, ← h, Finset.sum_eq_single w]
    · by_cases hw : w' = w
      · subst hw; simp
      · simp [Matrix.one_apply_ne hw, Pi.single_eq_of_ne (Ne.symm hw)]
    · intro u _ hu
      simp [Pi.single_eq_of_ne hu]
    · simp
  have hB' : B * Bᴴ = 1 := mul_eq_one_comm.mp hB
  refine ⟨Matrix.toLin'OfInv hB' hB, fun x => ?_⟩
  have hx : x = ∑ w, γ.g x w • b w := by
    apply γ.g.injective

    simp only [b, map_sum, map_smul, LinearEquiv.apply_symm_apply]
    ext u
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : (fun w : Fin 4 × ι => emb w.2 (x w.1))
      = B *ᵥ (fun w => φ (algebraMap K E (γ.g x w))) := by
    ext v
    have := congrArg (fun y => emb v.2 (y v.1)) hx

    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, map_sum, map_mul, hK] at this
    rw [this]
    simp [Matrix.mulVec, dotProduct, B, mul_comm, hK]
  rw [hv]
  change Bᴴ *ᵥ (B *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]

end GlobalTheory
end

section

open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.SerCmp.LabConv

theorem isCuspOf_of_hasCuspLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : Formalism.L2.NT.IsGenSys L.gen), t = L.teich → ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → GlobalTheory.GLq.IsCusp (fun x => V.character x) → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht L.gen hζ) V P → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) := by
  intro g _ L t ht hζ htL d V P hd hcusp hlab
  subst htL
  obtain ⟨hm, hi, hX, hdeg, hval⟩ := hlab
  rw [Fintype.card_fin] at hdeg
  have hPl : GlobalTheory.GLq.IsPrimeLab d P := ⟨hm, hi, Formalism.L2.NT.coeff_zero_ne_of_monic_irr hm hi hX, hdeg⟩
  refine ⟨hPl, hcusp, ?_⟩
  intro x hx y hy z hz
  have hd0 : 0 < d := hd
  have hcpl : GlobalTheory.GLq.IsPrimeLab d (y : GlobalTheory.GLq.Mt g d).charpoly := by
    refine ⟨Matrix.charpoly_monic _, hy, ?_, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]⟩
    intro h0
    have hdet := Matrix.det_eq_sign_charpoly_coeff (y : GlobalTheory.GLq.Mt g d)
    rw [h0, mul_zero] at hdet
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit y) |>.ne_zero hdet
  have hz1 : z ^ (g ^ d - 1) = 1 := GlobalTheory.GLq.LabelUnique.pow_sub_one_eq_one hcpl hz
  have hx1 : x ^ (g ^ d - 1) = 1 := GlobalTheory.GLq.LabelUnique.pow_sub_one_eq_one hPl hx
  have hprim : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := by
    rw [← L.gen_order d hd0]; exact IsPrimitiveRoot.orderOf _
  haveI : NeZero (g ^ d - 1) := ⟨by
    have := Nat.one_lt_pow hd0.ne' (Fact.out : g.Prime).one_lt
    omega⟩
  obtain ⟨m, -, hmz⟩ := hprim.eq_pow_of_pow_eq_one hz1
  have hax : aeval x P = 0 := GlobalTheory.GLq.LabelUnique.aeval_eq_zero_of_mem hm.ne_zero hx
  have haz : aeval z (y : GlobalTheory.GLq.Mt g d).charpoly = 0 :=
    GlobalTheory.GLq.LabelUnique.aeval_eq_zero_of_mem (Matrix.charpoly_monic _).ne_zero hz
  have hmz' : (Formalism.L2.NT.convC L.teich ht L.gen hζ).gen (Fintype.card (Fin d)) ^ m = z := by
    rw [Fintype.card_fin]; exact hmz
  have e := hval x hax y hy z haz m hmz'
  simp only [Fintype.card_fin, ZMod.card] at e
  have htx : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx1, map_one]
  show LinearMap.trace ℂ V (V.ρ y) = _
  rw [e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hmz, ← pow_mul, GlobalTheory.GLq.LabelUnique.thetaOf_gen_pow L d hd0 x htx]
  rfl

end GlobalTheory.SerCmp.LabConv
end
end
