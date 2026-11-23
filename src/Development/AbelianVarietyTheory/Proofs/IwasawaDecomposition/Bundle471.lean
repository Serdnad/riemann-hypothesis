module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle098
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle088
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle462
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle377
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle461
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFinitePointMovesVacuumToProjection
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
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.Brg


open _root_.Formalism.L2.Col in
theorem conjIdeal_eq_conjP {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = (conjPrime₂ P).asIdeal := by
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro r ⟨s, hs, e⟩
    show r ∈ (conjPrime₂ P).asIdeal
    rw [mem_conjP]
    have : cO E r = s := RingOfIntegers.ext (by
      show star (r : E) = (s : E)
      have e' : (r : E) = star (s : E) := e
      rw [e', star_star])
    rw [this]; exact hs
  · intro r hr
    rw [mem_conjP] at hr
    refine Ideal.subset_span ⟨cO E r, hr, ?_⟩
    show (r : E) = star (star (r : E))
    rw [star_star]


open _root_.Formalism.L2.Col in
theorem g_notMem_of_levOff {X : Fields} {Pr : Primes X} (hPr : Pr.Ok)
    (P : letI := X.starE; LevOff (E := X.E) ∅ Pr.vGs ∅) (k : Fin 2) :
    ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := by
  classical
  letI := X.starE
  intro hk
  have h0 : X.conjO (Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  have hsub : ∀ Q, Q ∈ Pr.vG k → Q ∈ Pr.vGs := fun Q hQ => by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ]
  rw [← hPr.piG_norm k] at hk
  rcases P.1.isPrime.mem_or_mem hk with h | h
  · have hc : conjPrime₂ P.1 ∈ Pr.vG k := by
      refine (mem_divs h0 _).2 ?_
      rw [mem_conjP]
      show cO X.E (X.conjO (Pr.piG k)) ∈ P.1.asIdeal
      exact (cO_cO (Pr.piG k)).symm ▸ h
    exact P.2.2.2 (conjPrime₂ P.1) (Or.inr (hsub _ hc)) (conjIdeal_eq_conjP P.1).symm
  · exact P.2.2.1 (Or.inr (hsub _ ((mem_divs h0 _).2 h)))

end GlobalTheory.Mem.R3.Brg

namespace GlobalTheory.Mem.R3.Brg

theorem muVal_eq {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hI : I.Ok) (hV : ValsIn I) (i : Fin B.R.m) {a : I.ι}
    {τ : Tup B.fields.F B.fields.E B.fields.K I.S} (hτ : I.tup a = τ) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (hg : ∀ k, ((B.host.g k : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal) (hu : (I.xi a).UnrAt P) :
    B.embLL ((I.Ch.muVal i P * xiValOf I τ P : B.LLˣ) : B.LL) = (((I.C.mu0 i * I.xi a).val P : ℂˣ) : ℂ) := by
  subst hτ
  rw [Formalism.L2.Host.HChar.val_mul, Units.val_mul, Units.val_mul, map_mul, hV.embLL_xiValOf a P hu]
  congr 1
  exact hI.ch_tied.muVal i P hg

theorem values : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    (∀ (i : Fin X.toD7.R.m) t, ∀ P ∈ (famR X I hX U Xg tr).A.ok t,
      X.toD7.what₂.embLL ((famR X I hX U Xg tr).A.muVal i t P : X.toD7.what₂.LL) =
        (((L.C.mu0 i * L.xiH t).val (P.1 : Pl X.toD7.host.E) : ℂˣ) : ℂ)) ∧
    (∀ P ∈ (famR X I hX U Xg tr).A.ok (famR X I hX U Xg tr).A.μ0,
      X.toD7.what₂.embLL ((famR X I hX U Xg tr).A.etaVal P : X.toD7.what₂.LL) =
        Formalism.L2.Host.etaAlg X.toD7.host L.C.eta (P.1 : Pl X.toD7.host.E)) ∧
    ∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → ∃ z : X.toD7.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP)) := by
  intro X px I hX U Xg tr L eG hI hV hL _
  classical
  letI := X.B.fields.starE
  have hPr : (X.B.primes px).Ok := (GlobalTheory.Mem.Col2.base_fields_primes_ok X.B px).2.1
  refine ⟨fun i t P hP => ?_, fun P _ => ?_, fun t PP hPP => ?_⟩
  · have hP' : P.1 ∈ Formalism.L2.DIV.offSet (E := X.B.fields.E) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ∅ := hP
    have hQ : ∀ PP, PP ∈ I.Q (ixOf I U t) → PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := fun PP h =>
      Finset.mem_union_right _ (by rw [← tup_ixOf I t]; exact h)
    have hg : ∀ k, ((X.B.host.g k : ℕ) : 𝓞 X.B.fields.E) ∉ P.1.asIdeal := g_notMem_of_levOff hPr P
    have hunr : (I.xi (ixOf I U t)).UnrAt P.1 := by
      by_contra hn
      rw [← hL.xiH t] at hn
      rcases (hL.is.Q_ram t P.1).1 hn with h | ⟨PP', h, hc⟩
      · rw [hL.Q t] at h
        exact hP'.2.1 (Or.inr (Finset.mem_coe.2 (hQ _ h)))
      · rw [hL.Q t] at h
        have hle : PP'.asIdeal ≤ (Formalism.L2.Col.conjPrime₂ P.1).asIdeal := fun c hcm => by
          obtain ⟨c', hc', e⟩ := hc c hcm
          refine (Formalism.L2.Col.mem_conjP (E := X.B.fields.E) P.1 c).2 ?_
          have : Formalism.L2.Col.cO X.B.fields.E c = c' := RingOfIntegers.ext e.symm
          rw [this]; exact hc'
        have heq : PP'.asIdeal = (Formalism.L2.Col.conjPrime₂ P.1).asIdeal :=
          PP'.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P.1).isPrime.ne_top hle
        exact hP'.2.2 PP' (Or.inr (Finset.mem_coe.2 (hQ _ h))) (heq.trans (conjIdeal_eq_conjP P.1).symm)
    rw [hL.C, hL.xiH t]
    exact muVal_eq I hI hV i (tup_ixOf I t) P.1 hg hunr
  · show X.B.embLL (I.Ch.etaVal P.1 : X.B.LL) = _
    rw [hL.C]
    exact hI.ch_tied.etaVal P.1
  · rcases hPP with h | h
    · rw [hL.Pg] at h
      obtain ⟨k, hk⟩ : ∃ k, PP ∈ (X.B.primes px).vG k := by
        rcases Finset.mem_union.1 h with h | h
        exacts [⟨0, h⟩, ⟨1, h⟩]
      have hn : Ideal.absNorm PP.asIdeal = X.B.host.g k := hPr.vG_norm k PP hk
      have hcard : Nat.card (kP PP) = X.B.host.g k := by
        rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hcard]
      exact (GlobalTheory.Core.Cls.coeffField_rootsOfUnity_typePrimes_hermitianStages X k).1
    · rw [hL.Q t] at h
      exact hV.2 _ PP h

end GlobalTheory.Mem.R3.Brg
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GeomConnFn

theorem isConnected_preimage {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp F)
    [LocallyOfFiniteType p]
    (h : ∀ a : X.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn p).range)
    (K : Type) [Field K] [Algebra F K] (U : X.Opens) (hU : IsAffineOpen U) (hx : genericPoint X ∈ U) :
    _root_.IsConnected
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K))) ⁻¹' (U : Set X)) := by
  let : Algebra F Γ(X, U) := (algX p U).toAlgebra
  let : Algebra F X.functionField := (GlobalTheory.Cartier.constFn p).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType F Γ(X, U) := hft
  let j : Γ(X, U) →ₐ[F] X.functionField :=
    { GlobalTheory.Cartier.fnOf U hx with
      commutes' := fun a => RingHom.congr_fun (GlobalTheory.Cartier.fnOf_comp_algX p U hx) a }
  have : IsDomain (K ⊗[F] Γ(X, U)) :=
    GlobalTheory.GeomConn.isDomain_tensor j (GlobalTheory.Cartier.fnOf_injective U hx) (fun a ha => h a ha) K
  have : IsDomain (Γ(X, U) ⊗[F] K) := (Algebra.TensorProduct.comm F Γ(X, U) K).toMulEquiv.isDomain
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have h1 : IsIntegral (pullback (hU.fromSpec ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap F K)))) := by
    rw [hg]
    exact IsIntegral.of_isIso (pullbackSpecIso F Γ(X, U) K).inv
  have h2 := IsIntegral.of_isIso
    (pullbackRightPullbackFstIso p (Spec.map (CommRingCat.ofHom (algebraMap F K))) hU.fromSpec).inv
  rw [← hU.range_fromSpec, ← Scheme.Pullback.range_snd]
  exact isConnected_range (Scheme.Hom.continuous _)

theorem geometricallyConnected_of_locallyOfFiniteType {F : Type} [Field F] [CharZero F] {X : Scheme.{0}}
    [IsIntegral X] (p : X ⟶ Sp F) [LocallyOfFiniteType p]
    (h : ∀ a : X.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn p).range) : GeometricallyConnected p := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => ?_⟩
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap F K))) :=
    ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  obtain ⟨x₀, hx₀⟩ := (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K)))).surjective (genericPoint X)
  refine connectedSpace_iff_univ.2 ⟨⟨x₀, trivial⟩, isPreconnected_of_forall x₀ fun y _ => ?_⟩
  obtain ⟨U, hU, hy, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (Opens.mem_top (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K))) y))
  have hg := GlobalTheory.Cartier.gen_mem hy
  refine ⟨_, Set.subset_univ _, ?_, hy, (isConnected_preimage p h K U hU hg).isPreconnected⟩
  rw [Set.mem_preimage, hx₀]
  exact hg

end GlobalTheory.GeomConnFn
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT


open Formalism.HermitianLatticesTheory GlobalTheory.ThetaMove in
theorem inverseHalfDifferent_local_trivial_at_prime_norm {R : Ranks} (H : Host R) (P : HeightOneSpectrum (𝓞 H.E)) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∉ P.asIdeal ^ 2) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (H.AA0 : Submodule (𝓞 H.E) H.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 H.E) H.E) := by
  have := P.isPrime
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hnd := GlobalTheory.PeriodIdealUnit.not_dvd_different (K := H.K) hp P.asIdeal hmem h2
  have hnot : ¬ H.𝔟 ≤ P.asIdeal := fun hle => hnd (by
    rw [H.𝔟_spec.1]
    exact (Ideal.dvd_iff_le.2 hle).mul_right _)
  obtain ⟨z, hz, hzP⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  have hB : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
      have h3 := H.𝔟_spec.2
      simp [h] at h3
  refine GlobalTheory.PeriodIdealUnit.locP_eq_one P _ ?_ ?_
  · intro t ht
    have ht' : t ∈ H.AA0 := ht
    unfold Host.AA0 at ht'
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff hB).1 ht' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hz))
    refine (mem_locP P 1 t).2 ⟨z, hzP, Submodule.mem_one.2 ⟨w, ?_⟩⟩
    rw [Algebra.smul_def, hw, mul_comm]
  · refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [one_smul]
    show (1 : H.E) ∈ H.AA0
    unfold Host.AA0
    refine (FractionalIdeal.mem_inv_iff hB).2 fun y hy => ?_
    rw [one_mul]
    exact FractionalIdeal.coeIdeal_le_one hy

theorem aaUnit_sall : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (I.J.amb B χ).AAUnit (Sall (Pr := B.primes X) I.sel (I.tup a) u) := by
  intro B X I hOk u a χ P hP
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr hOk.sel_ok
    (hOk.T_mem u) hOk.g_mem P hP
  show Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Th.perAA B.host ⊤) = _
  rw [Th.perAA_top]
  exact inverseHalfDifferent_local_trivial_at_prime_norm B.host P bad.2.1 bad.2.2.1

end GlobalTheory.Mem.Col2.AdT
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section



theorem GlobalTheory.Mem.Col2.TC.chartLev_off_type : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → ∀ (h1 : 1 ≤ B.R.m - 1) (β0 : Ch0 (B.R.m - 1)) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), (∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → ∀ x, x ∈ (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Uloc v ↔ x ∈ F.levJ.Uloc v := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF h1 β0 v hv x
  have hi : B.R.m - 1 ≤ (I.rec7 l Z).R.m := Nat.sub_le _ _
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) hi).1
  haveI : NeZero ((I.rec7 l Z).R.N (B.R.m - 1)) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s F.atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  obtain ⟨k, H⟩ := hF.mid (B.R.m - 1) h1 (succ_pred_m _)
  have hLbE : (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Lb = F.levJ.Lb := F.levJ_Lb h1 β0
  have hLb : ∀ x, x ∈ F.levJ.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N (B.R.m - 1)) (X.piT u) := by
    intro x
    rw [← hLbE]
    exact H.lb _ x
  have hL : F.levJ.Lb = rll_dLat ((I.rec7 l Z).R.N (B.R.m - 1)) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 F.levJ.Lb ?_
    rw [hF.piU]; exact hLb
  have hnb : v ∉ badG (I.rec7 l Z) := by
    rintro (h | h)
    · exact hv 0 h
    · exact hv 1 h
  by_cases hT : (((I.rec7 l Z).mem u).A.T : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal
  · have e1 := GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev F.atT.piU (s F.atT.piU) rfl hpq hTp (hLbE.trans hL) v hT (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u F.atT v hT) x
    have e2 := GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram F.levJ F.atT.piU (s F.atT.piU) rfl hpq hTp hL v hT (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u F.atT v hT) x
    rw [hLbE] at e1
    exact e1.trans e2.symm
  · have e1 := (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Uloc_hyp v hnb hT
    have e2 := F.levJ.Uloc_hyp v hnb hT
    rw [hLbE] at e1
    rw [e1, e2]
    exact Iff.rfl



theorem GlobalTheory.Mem.Col2.TC.chartLev_stab_vec : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → (∀ j v h, F.glevJ.fr j v h = 1) → ∀ (h1 : 1 ≤ B.R.m - 1) (β0 : Ch0 (B.R.m - 1)), ∃ w : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Fin (B.R.N (B.R.m - 1)) → kv (I.rec7 l Z).host.F v, ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) x, x ∈ (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Uloc v ↔ (x ∈ F.levJ.Uloc v ∧ ∀ j (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) *ᵥ w j v hv = w j v hv) := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF hfr h1 β0
  haveI : NeZero ((I.rec7 l Z).R.N (B.R.m - 1)) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  obtain ⟨w, hw⟩ := GlobalTheory.T.level_mem_chartLevel_iff_reduction_fixes_typePrime I hI hP l Z u F hF hfr h1 β0
  refine ⟨w, fun v x => ?_⟩
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) = 1 :=
    ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1
  by_cases hv : ∃ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal
  · have hput : ∀ (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f (badG (I.rec7 l Z))),
        x ∈ S.Uloc v ↔ rll_put ((I.rec7 l Z).R.N (B.R.m - 1)) v x ∈ S.U := by
      intro S
      constructor
      · intro hx
        have hxU := S.Uloc_le v hx
        rw [hgram] at hxU
        refine (S.U_eq _).2 ⟨?_, fun v' => ?_⟩
        · have := rll_put_mem_UAd (I.rec7 l Z).sp.cm ((I.rec7 l Z).R.N (B.R.m - 1)) v hxU
          rw [hgram]; exact this
        · by_cases e : v' = v
          · subst e; rw [rll_put_self]; exact hx
          · rw [rll_put_ne _ v v' e]; exact one_mem _
      · intro hx
        have := ((S.U_eq _).1 hx).2 v
        rwa [rll_put_self] at this
    rw [hput]
    constructor
    · intro hx
      have hJ : rll_put ((I.rec7 l Z).R.N (B.R.m - 1)) v x ∈ F.levJ.U := F.levJ_le h1 β0 hx
      have hxJ : x ∈ F.levJ.Uloc v := by
        have := ((F.levJ.U_eq _).1 hJ).2 v
        first
          | (convert this using 2; exact (rll_put_self _ v x).symm)
          | exact (congrArg (· ∈ F.levJ.Uloc v) (rll_put_self ((I.rec7 l Z).R.N (B.R.m - 1)) v x)).mp this
          | exact (rll_put_self ((I.rec7 l Z).R.N (B.R.m - 1)) v x) ▸ this
      exact ⟨hxJ, (hw v hv x hxJ).1 hx⟩
    · rintro ⟨hxJ, hs⟩
      exact (hw v hv x hxJ).2 hs
  · push_neg at hv
    rw [GlobalTheory.Mem.Col2.TC.chartLev_off_type I hI hP l Z u F hF h1 β0 v (fun j => hv j) x]
    exact ⟨fun h => ⟨h, fun j hj => absurd hj (hv j)⟩, fun h => h.1⟩

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
noncomputable section

namespace GlobalTheory.Mem.PrimesAtLevel

theorem not_both_mem {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hpP : (p : R) ∈ P) (hqP : (q : R) ∈ P) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  have h1 : ((a * p + b * q : ℤ) : R) = 1 := by rw [hab, Int.cast_one]
  push_cast at h1
  apply (inferInstance : P.IsPrime).ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hqP)

theorem primes_atT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (v : (I.atT l u a).vT), conjPrime₂ v.1 ≠ v.1 ∧ (∀ w ∈ (B.primes X).vGs, ¬ IsOver (v.1.under (𝓞 B.host.F)) w) ∧ (∀ P ∈ I.Q a, ¬ IsOver (v.1.under (𝓞 B.host.F)) P) ∧ Disjoint (B.primes X).vGs (I.Q a) := by
  intro B X I hI l u a v
  obtain ⟨P, hP⟩ := v
  dsimp only at hP ⊢
  have hpr := l.pr
  have hpiT : (B.primes X).piT u ∈ P.asIdeal := by
    unfold Primes.vT divs at hP
    split_ifs at hP with h
    · exact h.mem_toFinset.mp hP
    · simp at hP
  have hT : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hpr.piT_norm u]
    exact P.asIdeal.mul_mem_right _ hpiT
  have hTF : (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ (P.under (𝓞 B.host.F)).asIdeal := by
    show _ ∈ Ideal.comap (algebraMap _ _) _
    rw [Ideal.mem_comap, map_natCast]
    exact hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hc
    have h2 : B.fields.conjO ((B.primes X).piT u) ∈ P.asIdeal := by
      have h3 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal := by rw [hc]; exact hpiT
      exact (mem_conjP P _).mp h3
    obtain ⟨x, y, hxy⟩ := hpr.piT_cop u
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hxy]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpiT) (P.asIdeal.mul_mem_left _ h2)
  · intro w hw hov
    have hTw : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      rw [IsOver] at hov
      rw [hov, Ideal.mem_comap, map_natCast] at hTF
      exact hTF
    obtain ⟨i, hi⟩ : ∃ i, w ∈ (B.primes X).vG i := by
      classical
      rcases Finset.mem_union.mp hw with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hgw : (((B.primes X).g i : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      have hc : B.fields.conjO ((B.primes X).piG i) ∈ w.asIdeal := by
        unfold Primes.vG divs at hi
        split_ifs at hi with h
        · exact h.mem_toFinset.mp hi
        · simp at hi
      rw [← hpr.piG_norm i]
      exact w.asIdeal.mul_mem_left _ hc
    exact not_both_mem w.asIdeal (hpr.T_prime u) (hpr.g_prime i) (hpr.T_ne_g u i) hTw hgw
  · intro Q hQ hov
    obtain ⟨v, -, hsel, hgood⟩ := I.exists_of_mem_Q hQ
    have hv : v.asIdeal = (P.under (𝓞 B.host.F)).asIdeal := by
      rw [hov, ← hsel]
      exact (hI.sel_ok v).symm
    have hTv : (((B.primes X).T u : ℕ) : 𝓞 B.fields.F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem, hv]
      exact hTF
    have hd : ringChar (𝓞 B.fields.F ⧸ v.asIdeal) ∣ (B.primes X).T u := (ringChar.spec _ _).mp hTv
    rcases (Nat.dvd_prime (hpr.T_prime u)).mp hd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · apply hgood.2.2
      convert hI.T_mem u using 1
      exact h1
  · exact Finset.disjoint_right.mpr (Q_notMem_of_ok hI a)

end GlobalTheory.Mem.PrimesAtLevel
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts


theorem _root_.GlobalTheory.T.splitFinitePoint_moves_vacuum_to_projection : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), S.SigOK → T.SigOK → ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → GlobalTheory.Ker.IdemTwo w → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ (LT : Lt D.host.E T.rank) (L : Lt D.host.E r), IsSelfDualC T LT → SelfD X L → GlobalTheory.Ker.IsAA (latW hr L) LT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ h ∈ GfC S, SuppAt e S h → ∀ x : (AE D)ˣ, IsDetAt e S h x → ∀ Λ ∈ Vset D.host.E S.rank 1, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmtC S h) (stdL D.host.E S.rank) Λ → ∀ v : TF S.rank g, IsVac X bas w (tens (stdL D.host.E S.rank) L) v → ∀ (t : ℂ) (f : WO S T → ℂ), Zak ψ θ hr eT bas idx (frOf hr eT Z) (t • v) f → Zak ψ θ hr eT bas idx (frOf hr eT Z) ((t * (((χT x)⁻¹ : Circle) : ℂ) * ((Real.sqrt (((((Λ ⊓ stdL D.host.E S.rank).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).index ^ r : ℕ) : ℝ)) : ℝ) : ℂ)) • projA X bas w (tens Λ L) v) (om (h, 1) f) := by
  first | exact @GlobalTheory.OneMapRef.SplitProj.zak_om_split | exact GlobalTheory.OneMapRef.SplitProj.zak_om_split | (intros; apply GlobalTheory.OneMapRef.SplitProj.zak_om_split <;> assumption)
end
