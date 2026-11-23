module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle087
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle362
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle361
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle367
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle360
import Formalism.LocalToGlobal.Columns.Bundle032
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle131
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.MtHeckeLoc
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle467
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdLift

section General

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def sng (P : HeightOneSpectrum (𝓞 E)) (x : P.adicCompletion E) : AfE F E := (afIso F E).symm (Formalism.UG.P.afsplitF P x)

theorem adAt_sng_self (P : HeightOneSpectrum (𝓞 E)) (x : P.adicCompletion E) : adAt F P (sng F P x) = x := by
  rw [adAt_apply, sng]
  simp only [RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  exact Formalism.UG.P.afsplitF_self P x

theorem adAt_sng_ne {P w : HeightOneSpectrum (𝓞 E)} (h : w ≠ P) (x : P.adicCompletion E) : adAt F w (sng F P x) = 0 := by
  rw [adAt_apply, sng]
  simp only [RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  exact Formalism.UG.P.afsplitF_ne P w h x

def dev {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    Matrix (Fin n) (Fin n) (AfE F E) := (A - 1).map (sng F P)

theorem map_dev_self {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    (1 + dev F P A).map (adAt F P) = A := by
  ext i j
  simp only [dev, Matrix.map_apply, Matrix.add_apply, map_add (f := _), adAt_sng_self, Matrix.sub_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem map_dev_ne {n : ℕ} {P w : HeightOneSpectrum (𝓞 E)} (h : w ≠ P) (A : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    (1 + dev F P A).map (adAt F w) = 1 := by
  ext i j
  simp only [dev, Matrix.map_apply, Matrix.add_apply, map_add (f := _), adAt_sng_ne F h, Matrix.one_apply]
  split_ifs <;> simp

variable {F}

theorem mat_ext {n : ℕ} {M N : Matrix (Fin n) (Fin n) (AfE F E)} (h : ∀ w, M.map (adAt F w) = N.map (adAt F w)) : M = N := by
  ext i j
  exact PtExist.ad_ext fun w => congrFun (congrFun (h w) i) j

variable [StarRing E] (hc : CMData F E)

local notation "σ" => Formalism.UG.sigR hc.sig (FiniteAdeleRing (𝓞 F) F)

theorem map_cT_dev {n : ℕ} {P w : HeightOneSpectrum (𝓞 E)} (h : conjPrime₂ w ≠ P) (A : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    (cT σ (1 + dev F P A)).map (adAt F w) = 1 := by
  have key : ∀ x, adAt F w (σ (sng F P x)) = 0 := fun x => by
    have e := valued_sigR hc w (sng F P x)
    rwa [adAt_sng_ne F h, map_zero, Valuation.zero_iff] at e
  refine Matrix.ext fun i j => ?_
  show adAt F w (σ ((1 + dev F P A) j i)) = _
  simp only [dev, Matrix.map_apply, Matrix.add_apply, map_add (f := _), key, Matrix.one_apply]
  by_cases e : i = j
  · subst e; simp
  · simp [e, Ne.symm e]

theorem cT_cT {n : ℕ} (M : Matrix (Fin n) (Fin n) (AfE F E)) : cT σ (cT σ M) = M := by
  ext i j
  exact PtExist.sig_sig hc (M i j)

theorem exists_unitary {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} (hP : conjPrime₂ P ≠ P) (A : GL (Fin n) (P.adicCompletion E)) :
    ∃ z ∈ UAd hc n, (∀ w, w ≠ P → w ≠ conjPrime₂ P → ∀ i j, adAt F w (z.1 i j) = if i = j then 1 else 0) ∧
      ∀ i j, adAt F P (z.1 i j) = A.1 i j := by
  set g := 1 + dev F P A.1 with hg
  set g' := 1 + dev F P (A⁻¹).1 with hg'
  have h1 : g' * g = 1 := mat_ext fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    by_cases e : w = P
    · subst e
      rw [map_dev_self, map_dev_self, Units.inv_mul]
    · rw [map_dev_ne F e, map_dev_ne F e, mul_one]
  have h2 : cT σ g * cT σ g' = 1 := by rw [← cT_mul, h1, cT_one]
  have h3 : cT σ g * g = g * cT σ g := mat_ext fun w => by
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases e : w = P
    · subst e
      rw [map_cT_dev hc hP, mul_one, one_mul]
    · rw [map_dev_ne F e, mul_one, one_mul]
  have h4 : cT σ (g * cT σ g') * (g * cT σ g') = 1 := by
    rw [cT_mul, cT_cT, mul_assoc, ← mul_assoc (cT σ g), h3, mul_assoc, h2, mul_one, h1]
  refine ⟨⟨g * cT σ g', cT σ (g * cT σ g'), mul_eq_one_comm.1 h4, h4⟩, (PtExist.mem_uad_iff _).2 h4,
    fun w hw hw' i j => ?_, fun i j => ?_⟩
  · have e : (g * cT σ g').map (adAt F w) = 1 := by
      rw [Matrix.map_mul, map_dev_ne F hw, map_cT_dev hc (fun e => hw' (by rw [← e, CharValCompare.conjP_conjP])), mul_one]
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    exact this
  · have e : (g * cT σ g').map (adAt F P) = A.1 := by
      rw [Matrix.map_mul, map_dev_self, map_cT_dev hc hP, mul_one]
    exact congrFun (congrFun e i) j

end General

theorem exists_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ A : GL (Fin ((I.rec7 l Z).R.N i)) (P.1.adicCompletion B.fields.E), ∃ z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z = 1) ∧ ∀ r s, adAt B.host.F P.1 (z.1 r s) = A.1 r s := by
  intro B X I hI hP l Z a i hi P v hv A
  have hJ := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have hne : conjPrime₂ P.1 ≠ P.1 := fun e =>
    GlobalTheory.Proof.NarrowJetMoments.conjP_notMem_rowSG (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 hI.sel_ok hI.g_mem P.2
      (by rw [e]; exact P.2)
  have hs : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) P.1 x
  have hu : P.1.under (𝓞 B.host.F) = v := by
    rw [hs] at hv
    exact HeightOneSpectrum.ext (Eq.symm hv)
  obtain ⟨z, hz, h1, h2⟩ := exists_unitary (F := B.host.F) B.sp.cm hne A
  have key : ∀ v' : HeightOneSpectrum (𝓞 B.host.F), v' ≠ P.1.under (𝓞 B.host.F) → bc (prV (E := B.host.E) v') z = 1 := by
    intro v' hv'
    have e0 := AdPlace.bc_prV_eq_one_of_adAt _ _ _ v' z fun w hw => by
      have := (under_eq_iff B.host P.1 w).not.1 (hw ▸ hv')
      exact h1 w (fun e => this (Or.inl e)) fun e => this (Or.inr e)
    exact e0
  refine ⟨z, ?_, fun v' hv' => key v' fun e => hv' (e.trans hu), h2⟩
  rw [hJ]
  exact hz

end GlobalTheory.Mem.Col2.AdLift

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.AdT.PlaceUnder

theorem exists_star_ne {X : Fields} (hX : X.Ok) : ∃ x : X.E, star x ≠ x := by
  by_contra H
  push Not at H
  have := hX.cplxE
  obtain ⟨φ⟩ : Nonempty (X.E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal φ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, ← hX.conjE, H]

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : SBof I a), P.1 ∈ I.Q a → ∃ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∀ P' : SBof I a, P' ≠ P → ¬ Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P'.1) := by
  classical
  intro B X I hI _ l Z a P _
  have hseam : ∀ Q : HeightOneSpectrum (𝓞 B.fields.E), GlobalTheory.TwU.seamP (sm I l Z) Q = Q := by
    intro Q
    ext x
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) Q x
  obtain ⟨hX, -, -⟩ := base_fields_primes_ok B X
  have hc := (GlobalTheory.TopStepPrimes.primes_top_ok hI B.u₀ a).2.1
  refine ⟨HeightOneSpectrum.under (𝓞 (I.rec7 l Z).host.F) (GlobalTheory.TwU.seamP (sm I l Z) P.1), rfl, fun P' hne hov => ?_⟩
  rw [hseam, hseam] at hov
  have hu : P'.1.under (𝓞 B.fields.F) = P.1.under (𝓞 B.fields.F) := HeightOneSpectrum.ext (Eq.symm hov)
  rcases (GlobalTheory.NormOneUnit.under_eq_iff hX.star_F hX.rankE (exists_star_ne hX) P.1 P'.1).1 hu with h | h
  · exact hne (Subtype.ext h)
  · exact hc P.1 (Finset.mem_union_right _ P.2) (h ▸ Finset.mem_union_right _ P'.2)

end GlobalTheory.Mem.Col2.AdT.PlaceUnder
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (h : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
      ((y⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Λ := by
  apply le_antisymm
  · rw [Formalism.L2.PairingIndexBounds.F.latAd, Submodule.span_le]
    intro x hx
    exact Formalism.L2.GlobalTheoryTheory.Br.latLocGlob_main (F := F) Λ hfin x ((h _).2 hx)
  · intro x hx
    exact Submodule.subset_span ((h _).1 (Submodule.subset_span ⟨x, hx, rfl⟩))

theorem GlobalTheory.Mem.Col2.AdT.mvL_one {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.MainNotions.G.KAat.mvL (1 : GL (Fin N) E) Λ = Λ := by
  ext x
  simp only [Formalism.MainNotions.G.KAat.mvL, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Formalism.MainNotions.G.KAat.toLE_apply, Units.val_one, Matrix.one_mulVec, exists_eq_right]

theorem GlobalTheory.Mem.Col2.AdT.sup_dual_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    (d : Deco E n ST SG) (hd : d.Ok) (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal) (hcop : IsCoprime π (cO E π)) :
    d.L ⊔ Ideal.span {cO E π} • Formalism.HermitianLatticesTheory.dual (hStd E n) d.L = d.N := by
  ext x
  rw [GlobalTheory.Mem.Col2.MemLat.mem_N_iff d hd π hmem hcop, Submodule.mem_sup, Submodule.ideal_span_singleton_smul]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    exact ⟨y, hy, b, hb, rfl⟩
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact ⟨y, hy, _, Submodule.smul_mem_pointwise_smul _ _ _ hb, rfl⟩




theorem GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ c : (I.stp u a i).Cl, ((I.stp u a i).rep c).1.1.deco.1.N = GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) ((K (chOf c)).y ⟨c, rfl⟩).1 (K (chOf c)).lev.Lb := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K k hR c
  have hsp := (spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hG := hsp.1
  have hL := (hsp.2.2 u a).1 c
  have hf := (l.lat u a i c).fg
  rw [← hL] at hf
  have hA := (GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS _ _ _ (Module.Finite.iff_fg.2 hf)
      ((K (chOf c)).y_lat ⟨c, rfl⟩)).trans hL
  unfold GlobalTheory.TwU.latCo
  rw [hA, hG]
  unfold Formalism.L2.PairingIndexBounds.F.compan
  rw [GlobalTheory.Mem.Col2.AdT.mvL_one]
  have key := GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual (((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E))
    (fun x => rfl) ((I.stp u a i).rep c).1.1.deco.1.L
  unfold dualL at key
  erw [key]
  have hsep := sepElt_of_ok l.pr u
  have hmem : ∀ P : (B.primes X).vT u, (B.primes X).piT u ∈ P.1.asIdeal := fun P => by
    have := hsep.conj P
    rwa [cO_cO] at this
  exact (GlobalTheory.Mem.Col2.AdT.sup_dual_eq_N ((I.stp u a i).rep c).1.1.deco.1 ((I.stp u a i).rep c).1.1.deco.2 _ hmem (l.pr.piT_cop u)).symm
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi

open scoped TensorProduct

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
  (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))

def NearV (P : SBof I a)
    (x : GL (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (B.R.m - 1))) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))
    (g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) : Prop :=
  GlobalTheory.TwU.NearAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (GlobalTheory.Mem.Col2.ChartLevel.emb v x) (GlobalTheory.TwU.seamGL (sm I l Z) g)

def NearPair (P : SBof I a)
    (x : GL (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (B.R.m - 1))) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))
    (g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z : B.fields.K) : Prop :=
  GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z ∧ NearV I l Z a v P x g

def NearSet : Set (GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) :=
  {x | ∀ P : SBof I a, IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ g z, NearPair I l Z a v P x g z}


open Classical in
def valV (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) : ℂ :=
  (sm I l Z).σ₀ (∏ P : SBof I a,
    if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z then h.2.choose_spec.choose else 1)

end GlobalTheory.Mem.Col2.QChi

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TopRowsQ

open GlobalTheory.TopStep GlobalTheory.Mem.Col2 GlobalTheory.TopLaw

theorem redV_eq_of_cong {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {c : ℕ}
    (hc : 0 < c) {a b : Sp E n} (hb : b ∈ stdAt E n P) (h : (((qOf P : ℕ) : E) ^ c)⁻¹ • (a - b) ∈ stdAt E n P) :
    a ∈ stdAt E n P ∧ redV P a = redV P b := by
  have hq := qOf_ne_zero (P := P)
  have h1 : ∀ i, IntAt P ((((qOf P : ℕ) : E) ^ c)⁻¹ * (a i - b i)) := fun i => mem_stdAt.1 h i
  have h2 : ∀ i, IntAt P (a i - b i) := fun i => by
    have h3 := (intAt_pow (intAt_nat (P := P) (qOf P)) c).mul (h1 i)
    convert h3 using 1
    field_simp
  have ha : ∀ i, IntAt P (a i) := fun i => by
    have h3 := (h2 i).add (mem_stdAt.1 hb i)
    convert h3 using 1
    ring
  refine ⟨mem_stdAt.2 ha, funext fun i => ?_⟩
  have h4 : redP P (a i - b i) = 0 := by
    apply redP_eq_zero_of_div
    have h3 := (intAt_pow (intAt_nat (P := P) (qOf P)) (c - 1)).mul (h1 i)
    convert h3 using 1
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [reduction_sub (ha i) (mem_stdAt.1 hb i), sub_eq_zero] at h4
  exact h4

theorem lamQB_mul_levCong : ∀ {X : Fields} {R : Ranks} (ξ : Chr X.F X.E X.K) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (P : Q) (c M : ℕ), 1 ≤ M →
    ∀ (k : Formalism.L2.Col.GLint X.E (R.N R.m) P.1) (hk : k ∈ (levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).H)
    (g : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JQ P.1 (qOf P.1) R.r (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    CongE P.1 (2 * M) g (k⁻¹).1 →
    LocE.lamQB (resChar ξ P.1) R.r (R.N R.m - 1) g''.toLinearMap *
      (((levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).lam ⟨k, hk⟩ : X.Kˣ) : X.K) = 1 := by
  intro X R ξ Q P c M hM k hk g g'' hJ hpr hC
  have hN := N_m_succ R
  obtain ⟨j, hj, hb⟩ := (mem_levCong (N_m_succ R) c _ k).1 hk
  rw [levCong_lam (N_m_succ R) c _ hk hj hb, levRed_lam]
  have ek : redGL _ P.1 k = diagEmb _ (by omega : R.N R.m - 1 ≤ R.N R.m) (redGL _ P.1 j) := by
    have e := redGL_of_prinCong c.succ_pos hb
    rw [map_mul, map_inv, inv_mul_eq_one, redGL_extI] at e
    exact e.symm
  let g2 : Formalism.L2.Col.GLint X.E (R.N R.m - 1) P.1 := ⟨g'', hJ.1⟩
  have hred : redGL _ P.1 g2 = (redGL _ P.1 j)⁻¹ := by
    refine redGL_eq g2 fun x hx => ?_
    let v : Sp X.E (R.N R.m) := fun l => if h : l.1 < R.N R.m - 1 then x ⟨l.1, h⟩ else 0
    have hv : v ∈ stdAt X.E (R.N R.m) P.1 := mem_stdAt.2 fun l => by
      by_cases h : l.1 < R.N R.m - 1
      · simp only [v, dif_pos h]; exact mem_stdAt.1 hx _
      · simp only [v, dif_neg h]; simpa using intAt_nat (P := P.1) 0
    have hpv : prXpG X.E (R.N R.m) v = x := by
      funext i
      show v _ = x i
      simp only [v, dif_pos (show i.1 < R.N R.m - 1 from i.2)]
      rfl
    have hxg : g'' x = prXpG X.E (R.N R.m) (g v) := by
      have := LinearMap.congr_fun hpr v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hpv] at this
      exact this.symm
    obtain ⟨-, e1⟩ := redV_eq_of_cong (by omega : 0 < 2 * M) (glint_mem k⁻¹ hv) (hC v hv)
    have e2 := redV_redGL k⁻¹ hv
    rw [map_inv, ek, ← map_inv, diagEmb_val] at e2
    funext i
    have e3 := congrFun e1 (Br.iC hN i)
    rw [e2, (diagMat_mulVec hN _ _).1] at e3
    show redP P.1 (g'' x i) = _
    rw [hxg]
    refine e3.trans ?_
    congr 1
    funext l
    show redP P.1 (v (Br.iC hN l)) = redP P.1 (x l)
    simp only [v, Br.iC, dif_pos l.2]
  have hH : redGL _ P.1 g2 ∈ HQ (𝓞 X.E ⧸ P.1.asIdeal) (R.N R.m - 1) R.r (R.m * R.t) := hred ▸ inv_mem hj
  have hl := lamQB_eq_red (resChar ξ P.1) (rank_X'_eq R) g2 hH
  rw [show (g''.toLinearMap : HomE X.E _ _) = g2.1.toLinearMap from rfl, hl]
  have e4 : lamQ (resChar ξ P.1) _ R.r (R.m * R.t) ⟨redGL _ P.1 g2, hH⟩ =
      (lamQ (resChar ξ P.1) _ R.r (R.m * R.t) ⟨redGL _ P.1 j, hj⟩)⁻¹ := by
    rw [← map_inv]
    exact congrArg _ (Subtype.ext hred)
  rw [← Units.val_mul, e4]
  show (((_ : X.Kˣ)⁻¹)⁻¹ * (lamQP ξ P.1 (R.N R.m - 1) R.r (R.m * R.t) ⟨redGL _ P.1 j, hj⟩)⁻¹ : X.Kˣ).1 = 1
  rw [inv_inv, lamQP, mul_inv_cancel, Units.val_one]

end GlobalTheory.TopRowsQ
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

theorem levQ_of_congE {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) (j : ℕ) (hj : j < R.m) (b : L.β j) (P : rowSG Pr sel mu)
    (hP : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (g : Formalism.L2.Col.GLint X.E (R.N j) P.1)
    (h1 : ∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 ^ cst.D P : ℕ) : X.E)⁻¹ • (g.1 x - x) ∈ stdAt X.E (R.N j) P.1) :
    ∃ h : g ∈ (L.levQ j b ⟨P.1, hP⟩).H, (L.levQ j b ⟨P.1, hP⟩).lam ⟨g, h⟩ = 1 := by
  have m := GlobalTheory.TwU.MidIndep.extE_cong_mem hL j hj b P g.1 h1
    (GlobalTheory.TwU.MidIndep.cong_inv P.1 _ _ (hL.cst_ok.D_pos P) g.1 h1)
  have hx := GlobalTheory.CongLevel.extE_inX (cOf R j) g.1
  have hmem : g ∈ (L.levQ j b ⟨P.1, hP⟩).H := by
    rw [hL.grpQ j b ⟨P.1, hP⟩, Subgroup.mem_subgroupOf]
    exact ⟨_, m.1, hx⟩
  refine ⟨hmem, Units.ext ?_⟩
  rw [hL.chrQ j b ⟨P.1, hP⟩ ⟨g, hmem⟩ _ m.1 hx]
  exact m.2

theorem levQ_deep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (j : ℕ), j < B.R.m → ∀ (b : (I.idx a).β j) (P : SBof I a) (hP : P.1 ∈ I.Q a) (g : Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1), CongE P.1 ((I.cst a).D P) g.1 1 → ∃ h : g ∈ ((I.idx a).levQ j b ⟨P.1, hP⟩).H, ((I.idx a).levQ j b ⟨P.1, hP⟩).lam ⟨g, h⟩ = 1 := by
  intro B X I hOk a j hj b P hP g hg
  refine levQ_of_congE (hOk.idx_ok a) j hj b P hP g fun x hx => ?_
  rw [Nat.cast_pow]
  exact hg x hx

end GlobalTheory.Mem.Col2.AdT

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

theorem _root_.GlobalTheory.T.frameTransport_eta_supported_at_placeIdempotent : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ → SuppAt e V α := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.eta_suppAt | exact GlobalTheory.Mem.R3.LiftBrg.eta_suppAt | (intros; apply GlobalTheory.Mem.R3.LiftBrg.eta_suppAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



theorem _root_.GlobalTheory.T.exists_unitaryGroups_equiv_unitForm_gram_one : ∀ (X : Stages) (i : Fin X.toD7.R.m), (Vc X.toD7 i).gram = 1 →
    ∃ (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i))
      (eΓ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV ≃* GQ (Vc X.toD7 i)),
      (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) ∧
      (∀ γ, Bridge.ratF (Vc X.toD7 i) (eΓ γ) = eG (Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV γ)) ∧
      (∀ γ, Bridge.IsRatMat (Vc X.toD7 i) (eΓ γ) (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.StdGroups.stdGroups_equiv | exact GlobalTheory.Mem.R3.LiftBrg.StdGroups.stdGroups_equiv | (intros; apply GlobalTheory.Mem.R3.LiftBrg.StdGroups.stdGroups_equiv <;> assumption)
end
