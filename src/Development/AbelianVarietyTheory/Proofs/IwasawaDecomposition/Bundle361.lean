module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle270
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle332
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle343
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Formalism.LocalRingCardinality.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle342
public import Formalism.LocalToGlobal.Columns.Bundle015
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle098
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle177
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle341
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004

@[expose] public section

section

noncomputable section

namespace GlobalTheory.HeightCounting.TrueConjLabels

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne Pointwise

section General

variable {Ω : Type} [Field Ω]

theorem val_lt_iff {A B : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ x, x ∈ A ↔ c x ∈ B) (y : Ω) :
    B.valuation (c y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← hc, ← map_inv₀, ← hc, map_eq_zero_iff _ c.injective]

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

theorem exists_transport_elt (s : E ≃+* E) (c : Ω ≃+* Ω) (hs : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (s x))
    (t : G E Ω) : ∃ γ : G E Ω, ∀ x, γ (c x) = c (t x) := by
  refine ⟨{ (c.symm.trans (t.toRingEquiv.trans c)) with commutes' := fun y => ?_ }, fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := s.surjective y
    show c (t (c.symm _)) = _
    rw [← hs, c.symm_apply_apply, t.commutes]
  · show c (t (c.symm (c x))) = _
    rw [c.symm_apply_apply]

end General

section Host

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def conjInt (H : Host R) : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem coe_conjInt (x : 𝓞 H.E) : ((conjInt H x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := rfl

theorem isConjPl_iff {w w' : PlE H} : IsConjPl H w w' ↔ ∀ x, x ∈ w.asIdeal ↔ conjInt H x ∈ w'.asIdeal := by
  refine ⟨fun h x => h x _ (coe_conjInt x), fun h x y hy => ?_⟩
  have : y = conjInt H x := RingOfIntegers.ext (hy.trans (coe_conjInt x).symm)
  rw [this]; exact h x

theorem eq_of_isConjPl {w₀ w₁ w : PlE H} (h₀ : IsConjPl H w₀ w) (h₁ : IsConjPl H w₁ w) : w₀ = w₁ := by
  apply HeightOneSpectrum.ext
  ext x
  rw [isConjPl_iff.1 h₀, isConjPl_iff.1 h₁]

theorem exists_ext (N : NData R H what₂) {w₀ w : PlE H} (h : IsConjPl H w₀ w) : ∃ c : N.Om ≃+* N.Om,
    (∀ x : H.E, c (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x)) ∧
    ∀ x, x ∈ N.plOm.1 w₀ ↔ c x ∈ N.plOm.1 w := by
  let c₀ : N.Om ≃+* N.Om := IsAlgClosure.equivOfEquiv N.Om N.Om H.conj.toRingEquiv
  have h₀ : ∀ x : H.E, c₀ (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x) := fun x =>
    IsAlgClosure.equivOfEquiv_algebraMap N.Om N.Om H.conj.toRingEquiv x
  let B : ValuationSubring N.Om := (N.plOm.1 w₀).comap c₀.symm.toRingHom
  have hB : ∀ x, x ∈ N.plOm.1 w₀ ↔ c₀ x ∈ B := fun x => by
    simp [B, ValuationSubring.mem_comap]
  have hBw : IsPlaceOver (F := H.E) B w := fun y => by
    obtain ⟨x, rfl⟩ := (conjInt H).surjective y
    rw [coe_conjInt, ← h₀, val_lt_iff c₀ hB, ← isConjPl_iff.1 h]
    exact N.plOm.2 w₀ x
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hBw (N.plOm.2 w)
  refine ⟨c₀.trans σ.toRingEquiv, fun x => ?_, fun x => ?_⟩
  · show σ (c₀ _) = _
    rw [h₀, σ.commutes]
  · show _ ↔ σ (c₀ x) ∈ _
    rw [hB, ← hσ, ← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul_iff.symm

end Host

theorem exists_gamma (D : D7) (k : Fin 2) : ∃ γ : PlE D.host → G D.host.E D.nd.Om,
    (∀ v, γ (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    ∀ v w, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ w (c x) = c (D.ntypes.tg k v x) := by
  have key : ∀ w : PlE D.host, ∃ γ : G D.host.E D.nd.Om, (∀ v, w = D.naut.plGw k v → γ = D.ntypes.tg k v) ∧
      ∀ v, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ (c x) = c (D.ntypes.tg k v x) := by
    intro w
    by_cases h : ∃ v, IsConjPl D.host (D.naut.plGw k v) w
    · obtain ⟨v, hv⟩ := h
      obtain ⟨c, h1, h2⟩ := exists_ext D.nd hv
      obtain ⟨γ, hγ⟩ := exists_transport_elt D.host.conj.toRingEquiv c h1 (D.ntypes.tg k v)
      refine ⟨γ, fun v' e => absurd (e ▸ hv) (D.naut.plGw_nconj k v v'), fun v' hv' => ?_⟩
      obtain rfl : v = v' := D.naut.plGw_inj k (eq_of_isConjPl hv hv')
      exact ⟨c, h1, h2, hγ⟩
    · refine ⟨Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1) w, fun v e => ?_, fun v hv => absurd ⟨v, hv⟩ h⟩
      rw [e]; exact (D.naut.plGw_inj k).extend_apply _ _ v
  choose γ h1 h2 using key
  exact ⟨γ, fun v => h1 _ v rfl, fun v w hw => h2 w v hw⟩



theorem exists_labels_true_conj : ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (Rw : RowWD D), ∃ lab h A C tm tg hl,
    (∀ k v, A.plGw k v = D.naut.plGw k v) ∧
    ∃ T : GlobalTheory.RowTie.WDTie (setAut D hE lab h A C tm tg hl).nd (setAut D hE lab h A C tm tg hl).naut,
      LabTrue (setAut D hE lab h A C tm tg hl) T ∧ LabConj (setAut D hE lab h A C tm tg hl) T ∧
      ∃ Rs : RowSide (setAut D hE lab h A C tm tg hl),
        (∀ σ w, T.e w (Rs.locR σ w) = Rw.par σ w) ∧ ∀ σ w, Rs.satR σ w = Rw.sat σ w := by
  intro D hE Rw
  have hS : ∀ k v, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    fun k v => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  let lab : ∀ k, D.what₂.FT → D.nd.PlG k → Polynomial (ZMod (D.host.g k)) := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (Rw.par σ (D.naut.plGw k v))
  have h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = D.R.r := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ⟨WD.lab_monic _ _ _, ((WD.natDegree_lab_eq_iff (hS k v) _).2 (Rw.tame σ k v)).trans (Rw.dim σ _)⟩
  choose γ hγ1 hγ2 using exists_gamma D
  let A : NAut (ndLab D.nd lab h) := nAutWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj
    D.naut.plGw_nconj D.ntypes.teichC γ
  have hA : ∀ k v (a : A.LP (A.plGw k v)), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.items₂ k (A.plGw k v) a = WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (show WDAt D.nd (D.naut.plGw k v) from a) := fun k v a => by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exact congrArg (fun x => WD.lab (h := D.nd.plOm.2 (D.naut.plGw k v)) (D.ntypes.teichC k) x (show WDAt D.nd (D.naut.plGw k v) from a)) (hγ1 k v)
  have hl : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod := by
    intro k v L hL
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    rw [hA k v L] at hL ⊢
    exact WD.inePol_eq_of_natDegree_lab _ _ _ hL
  obtain ⟨C⟩ := GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc _ _ _ _ A hE
  refine ⟨lab, h, A, C, D.ntypes.tg_mem, D.ntypes.tg_gen, hl, fun _ _ => rfl,
    wdTieWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj D.naut.plGw_nconj D.ntypes.teichC γ,
    fun k v a => hA k v a, fun k v w hw => ?_, ⟨Rw.par, Rw.sat, fun k σ v => (hA k v _).symm⟩, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c, h1, h2, h3⟩ := hγ2 k v w hw
  exact ⟨c, γ k w, h1, h2, h3, fun _ => rfl⟩

end GlobalTheory.HeightCounting.TrueConjLabels

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial

theorem exists_setAut_wdTie_labConj : ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (Rw : RowWD D), ∃ lab h A C tm tg hl, (∀ k v, A.plGw k v = D.naut.plGw k v) ∧ ∃ T : GlobalTheory.RowTie.WDTie (setAut D hE lab h A C tm tg hl).nd (setAut D hE lab h A C tm tg hl).naut, LabTrue (setAut D hE lab h A C tm tg hl) T ∧ LabConj (setAut D hE lab h A C tm tg hl) T ∧ ∃ Rs : RowSide (setAut D hE lab h A C tm tg hl), (∀ σ w, T.e w (Rs.locR σ w) = Rw.par σ w) ∧ ∀ σ w, Rs.satR σ w = Rw.sat σ w :=
  TrueConjLabels.exists_labels_true_conj

end GlobalTheory.HeightCounting

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumns_periodMapDatum_ok_and_over_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.perIn u a).Ok ∧ (I.perIn u a).Over (I.atIn u a) := by
  first | exact @GlobalTheory.Mem.Col2.PerLaw.perIn_laws | exact GlobalTheory.Mem.Col2.PerLaw.perIn_laws | (intros; apply GlobalTheory.Mem.Col2.PerLaw.perIn_laws <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistPlaces_prime_to_levelAndTypePrimes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws → ∀ (u : B.Word) (a : I.ι) (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad | exact GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad | (intros; apply GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_adelicPoint_decoratedLattice_allTwists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (n : ℕ) (p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs I.SQ), ∃ g : GA B n, PtOf g p := by
  first | exact @GlobalTheory.Mem.Col2.PtTwist.exists_ptOf_twists | exact GlobalTheory.Mem.Col2.PtTwist.exists_ptOf_twists | (intros; apply GlobalTheory.Mem.Col2.PtTwist.exists_ptOf_twists <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.stepZeroHermitianLevel_uniformiser_kills_values_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u)), SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1) (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) → ∃ L' : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u), L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧ ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) → ∀ m : L'.fM w h, a • m = 0 := by
  first | exact @GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values | exact GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values | (intros; apply GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix


theorem _root_.GlobalTheory.T.couplingCoset_frames_invariant_rational_unitary : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (j : ℕ), X.Ok → Pr.Ok → ∀ (q q' : PtAt R sel mu cst u j) (γ : UF X.E (R.N j)), q'.1.1 = ((γ, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • q.1.1 → q'.1.2 = (fun z => γ.1 z) '' q.1.2 → cosetIn q' = cosetIn q := by
  exact @GlobalTheory.Mem.Col2.cosetIn_smul_unitary
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TwistPrimes

open GlobalTheory.Mem.LevTwist ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

theorem twist_primes_away : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (I.Q I.mu0 = ∅) ∧ ∀ (u : B.Word) (a : I.ι), ∀ P ∈ I.Q a, (P ∉ (B.primes X).vT u ∧ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ (B.primes X).vT u ∧ conjPrime₂ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ I.Q a) ∧ X.piT u ∉ P.asIdeal ∧ (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  intro B X I h
  refine ⟨I.twistPrimes_reference_tuple_eq_empty, fun u a P hP => ?_⟩
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hg := good_of_mem h (I.Q_subset_SQ a hP)
  have hS := hg.2.2.2
  have hu : (conjPrime₂ P).under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := (under_eq_iff B.host P _).2 (Or.inr rfl)
  have hT : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      ((B.primes X).T u : 𝓞 B.host.E) ∉ R.asIdeal := fun R hR hm => hS (by
    rw [← hR, (ReadTwist.plc_under_eq_iff (F := B.host.F) R (hPr.T_prime u)).2 hm]
    exact h.T_mem u)
  have hpi : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      (B.primes X).piT u ∉ R.asIdeal := fun R hR hm => hT R hR (by
    rw [← hPr.piT_norm u]; exact Ideal.mul_mem_right _ _ hm)
  have h0 : (B.primes X).piT u ≠ 0 := fun e => by
    have := hPr.piT_norm u
    rw [e, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hvT : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      R ∉ (B.primes X).vT u := fun R hR hm => hpi R hR ((mem_divs h0 _).1 hm)
  have hvG : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      R ∉ (B.primes X).vGs := fun R hR hm => hS (by rw [← hR]; exact plc_mem h hm)
  refine ⟨⟨hvT P rfl, hvG P rfl, hvT _ hu, hvG _ hu, fun hc => ?_⟩, hpi P rfl, fun hm => hT P rfl ?_⟩
  · have e := (good_of_mem h (I.Q_subset_SQ a hc)).1
    rw [hu, hg.1] at e
    exact conjP_ne B.host ((GoodPlace.goodPl_under_iff _ B.host _ P).1 hg.2).1 e.symm
  · rw [← map_natCast (algebraMap (𝓞 B.host.F) (𝓞 B.host.E))]
    exact hm

end GlobalTheory.Mem.Col2.TwistPrimes
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dualLattice_class_localization_eq_unimodularCompanion : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Y : DivX (I.rec7 l Z)) (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (j : ℕ), j ≤ B.R.m → ∀ (c : (I.stp u μ j).Cl), Submodule.IsLattice B.fields.E ((I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ∧ ∀ x : Fin (B.R.N j) → B.fields.E, (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ↔ (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ ((I.stp u μ j).rep c).1.1.deco.1.N) := by
  first | exact @GlobalTheory.LshOffLevel.lsh_lattice_and_loc_eq | exact GlobalTheory.LshOffLevel.lsh_lattice_and_loc_eq | (intros; apply GlobalTheory.LshOffLevel.lsh_lattice_and_loc_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
open Formalism.MainNotions Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Col2.TopCh
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopStepPrimes

open IsDedekindDomain.HeightOneSpectrum GlobalTheory.TopStep

theorem reduction_eq_zero_of_valuation_le {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {x : E}
    (h : P.valuation E x ≤ WithZero.coe (Multiplicative.ofAdd (-((1 : ℕ) : ℤ)))) : redP P x = 0 := by
  have hlt : P.valuation E x < 1 := h.trans_lt (by decide)
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer x hlt.le
  have hd : (d : 𝓞 E) ∉ P.asIdeal := d.2
  have hdv : P.valuation E (algebraMap (𝓞 E) E d) = 1 := by
    rw [valuation_of_algebraMap]
    exact le_antisymm (P.intValuation_le_one _) (not_lt.1 fun hc => hd ((P.intValuation_lt_one_iff_mem _).1 hc))
  have hn : n ∈ P.asIdeal := by
    rw [← P.valuation_lt_one_iff_mem (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E n) < 1
    rw [← hnd, map_mul, hdv, mul_one]
    exact hlt
  have hs := reduction_spec P hd (a := x) (r := n) (by rw [mul_comm]; exact hnd)
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hn] at hs
  exact (mul_eq_zero.1 hs).resolve_left (mk_ne_zero hd)

theorem redGL_eq_one_of_lqPrinc {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (g : GLint E n P) (hg : lqPrinc P 1 (g : Sp E n ≃ₗ[E] Sp E n)) : redGL n P g = 1 := by
  apply Units.ext
  rw [redGL_val]
  ext i j
  have h2 : LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) i j = g.1 (Pi.single j 1) i := by
    rw [LinearMap.toMatrix'_apply]
    rfl
  have hv := hg i j
  rw [Matrix.sub_apply, h2] at hv
  have hx := glint_entry g i j
  have hδ : IntAt P ((1 : Matrix (Fin n) (Fin n) E) i j) := by
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using intAt_one
    · simpa [Matrix.one_apply, hij] using intAt_zero
  have hr : redP P ((1 : Matrix (Fin n) (Fin n) E) i j) = (1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j := by
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using reduction_one₂
    · simpa [Matrix.one_apply, hij] using reduction_zero
  have e : g.1 (Pi.single j 1) i = (g.1 (Pi.single j 1) i - (1 : Matrix (Fin n) (Fin n) E) i j) +
      (1 : Matrix (Fin n) (Fin n) E) i j := by ring
  show redP P (g.1 (Pi.single j 1) i) = _
  rw [e, reduction_add (intAt_sub hx hδ) hδ, reduction_eq_zero_of_valuation_le hv, zero_add, hr]
  rfl

end GlobalTheory.TopStepPrimes


open GlobalTheory.TopStepPrimes in
theorem GlobalTheory.TopStepPrimes.primes_top_ok : ∀ {B : Base} {X : PreX B.toPre} {I : TC B X}, I.Ok → ∀ (u : B.Word) (a : I.ι), Disjoint (B.primes X).vGs (I.Q a) ∧ (∀ P ∈ uSG ∅ (uSG (B.primes X).vGs (I.Q a)), conjPrime₂ P ∉ uSG ∅ (uSG (B.primes X).vGs (I.Q a))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.fields.E (B.R.N B.R.m - 1) P.1)), lqPrinc P.1 1 (g : Sp B.fields.E (B.R.N B.R.m - 1) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N B.R.m - 1)) → ∃ h : g ∈ (levQX B.R I.sel (I.tup a) P).H, (levQX B.R I.sel (I.tup a) P).lam ⟨g, h⟩ = 1 := by
  intro B X I h u a
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.Mem.LevTwist.levOk_twists B X I h).2.1.mono_right (I.Q_subset_SQ a)
  · intro P hP
    have h1 := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
    unfold Sall at h1
    simp only [Finset.mem_union] at h1 hP ⊢
    rcases hP with h0 | hP
    · exact absurd h0 (Finset.notMem_empty _)
    · rintro (hc | hc)
      · exact Finset.notMem_empty _ hc
      · exact (h1 P (Or.inr hP)).1 (Or.inr hc)
  · intro P g hg
    have e := redGL_eq_one_of_lqPrinc g hg
    refine ⟨(mem_levQX _ _ _ _).2 (e ▸ Subgroup.one_mem _), ?_⟩
    rw [levQX_lam]
    have key : ∀ {G M : Type} [Group G] [Monoid M] (H : Subgroup G) (f : H →* M) (y : G) (hy : y ∈ H), y = 1 → f ⟨y, hy⟩ = 1 := by
      rintro G M _ _ H f y hy rfl
      exact map_one f
    exact key _ _ _ _ e
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

theorem _root_.GlobalTheory.T.chainStep_weight_arithmetic : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (μ : I.ι) (i : ℕ), i < B.R.m →
    ∃ k : (I.rec7 l Z).what₂.Tau → ℕ,
      (∀ τ, (k τ : ℤ) = shiftOf (lamTG (I.fm l u μ) i) τ + ((I.rec7 l Z).chTw u μ).sSharp i τ) ∧
      ∀ τ r, nuT (I.rec7 l Z) u i τ r = ((I.fm l u μ).lam i τ).natW r + k τ := by
  exact @GlobalTheory.IntegralityCompare.weight_arith_step
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.charpoly_coeff_congr_same_place_alt : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → ∀ (σ : D.what₂.FT) (i i' : X.nd.Loc), X.nd.w i = X.nd.w i' → ∀ (Sig Sig' : List (Formalism.BasicNotions.Part Y.naut.CG)) (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (ρ' : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i')), HasParamW X.nd Y.naut i σ Sig → IsRepOfSig X.nd Y.naut i Sig ρ → HasParamW X.nd Y.naut i' σ Sig' → IsRepOfSig X.nd Y.naut i' Sig' ρ' → ∀ (g : G D.host.E X.nd.Om) (n : ℕ), iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) - iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈ (Pl.plB (X.nd.w i)).nonunits := by
  first | exact @GlobalTheory.HeightCounting.charpoly_coeff_congr_same_place | exact GlobalTheory.HeightCounting.charpoly_coeff_congr_same_place | (intros; apply GlobalTheory.HeightCounting.charpoly_coeff_congr_same_place <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localisation_formLattice_iff_classValues_weylLattice : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (Pl : Rows.Places K) (w : Pl.Pl) (p : ℕ) [Fact p.Prime] (iL : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖iL x‖ ≤ 1) → ∀ x : S.FormsK emb lam h, x ∈ locW Pl w (S.latOf emb lam h fun c => delAtr emb lam (S.Lsh c.1 (S.rep c))) ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  first | exact @GlobalTheory.Mem.Col2.GStep.locW_latOf_iff | exact GlobalTheory.Mem.Col2.GStep.locW_latOf_iff | (intros; apply GlobalTheory.Mem.Col2.GStep.locW_latOf_iff <;> assumption)
end
