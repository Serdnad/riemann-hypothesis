module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle259
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle260
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem.FieldsLaws

open Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g :=
  (H.gal).apply_symm_apply g

theorem sigmaOf_galE (σ : H.E ≃ₐ[ℚ] H.E) : H.sigmaOf (H.galE σ) = σ :=
  (H.gal).symm_apply_apply σ

theorem gal_comm (s t : H.E ≃ₐ[ℚ] H.E) : s * t = t * s := by
  apply (H.gal).injective
  rw [map_mul, map_mul, mul_comm]

theorem mem_K_iff (x : H.E) : x ∈ H.K ↔ ∀ τ : R.Psi, H.sigmaOf τ x = x := by
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  have key : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ H.K.fixingSubgroup ↔ H.galE σ ∈ R.Psi := by
    intro σ
    rw [H.galE_mem_Psi_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h
      exact h _ (IntermediateField.mem_adjoin_simple_self ℚ _)
    · intro h y hy
      have hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
        refine IntermediateField.adjoin_simple_le_iff.2 ?_
        rw [IntermediateField.mem_fixedField_iff]
        intro f hf
        have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ (H.sqd) := by
          rw [Subgroup.zpowers_le]
          exact h
        exact this hf
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hy) σ (Subgroup.mem_zpowers σ)
  constructor
  · intro hx τ
    have h : H.sigmaOf τ ∈ H.K.fixingSubgroup := by
      rw [key, galE_sigmaOf]
      exact τ.2
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h x hx
  · intro hx
    rw [← IsGalois.fixedField_fixingSubgroup H.K, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have := hx ⟨_, (key σ).1 hσ⟩
    rwa [sigmaOf_galE] at this

theorem unram (P : HeightOneSpectrum (𝓞 H.E)) :
    ¬ (P.asIdeal.comap (algebraMap (𝓞 H.F) (𝓞 H.E))).map (algebraMap (𝓞 H.F) (𝓞 H.E)) ≤ P.asIdeal ^ 2 := by
  have hcm : IsCMField H.E := H.isCMField_hostE
  intro hle
  obtain ⟨π, hπ⟩ := (P.under (𝓞 H.F)).intValuation_exists_uniformizer
  have hmem : π ∈ (P.under (𝓞 H.F)).asIdeal := by
    have := ((P.under (𝓞 H.F)).intValuation_le_pow_iff_mem π 1).1 (by rw [hπ]; simp)
    rwa [pow_one] at this
  have h2 : algebraMap (𝓞 H.F) (𝓞 H.E) π ∈ P.asIdeal ^ 2 := hle (Ideal.mem_map_of_mem _ hmem)
  have h3 := (P.intValuation_le_pow_iff_mem _ 2).2 h2
  have h4 := HostCM.valuation_eq_of_unram H.E (fun P hP h0 h =>
    H.der.unramEF P hP h0 fun x => by
      have hx : H.conj • x = IsCMField.complexConj H.E • x :=
        RingOfIntegers.ext (H.φ₀.injective ((H.conjE_apply H.φ₀ x).trans
          (IsCMField.complexEmbedding_complexConj H.E H.φ₀ x).symm))
      rw [hx]
      exact h x) P (π : H.F)
  have h5 : P.valuation H.E (algebraMap (𝓞 H.E) H.E (algebraMap (𝓞 H.F) (𝓞 H.E) π)) =
      (P.under (𝓞 H.F)).valuation H.F (algebraMap (𝓞 H.F) H.F π) := h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hπ] at h5
  rw [h5, WithZero.exp_le_exp] at h3
  omega

end Host

variable (B : Base)

theorem embLL_comp_embBar (τ : Tau B.R) :
    B.embLL.comp (B.fields.embBar τ) = B.host.emb ((τ : B.R.GG) * B.R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp, ← B.fields_embC]
  refine RingHom.ext fun x => ?_
  exact congrArg (fun y => B.embLL (B.tauLL τ y)) (B.fields_sig x)

theorem embLL_comp_emb (τ : Tau B.R) : B.embLL.comp (B.fields.emb τ) = B.host.emb (τ : B.R.GG) :=
  B.fields_embC τ

theorem mem_Kq_iff (x : B.host.E) : x ∈ B.fields.Kq ↔ x ∈ B.host.K := by
  rw [mem_K_iff]
  constructor
  · intro h τ
    have h1 := B.embE.injective (h τ (1 : B.R.Psi))
    have h2 : B.host.sigmaOf ((1 : B.R.Psi) : B.R.GG) = 1 := map_one (B.host.gal).symm
    have h3 : B.host.sigmaOf τ x = B.host.sigmaOf ((1 : B.R.Psi) : B.R.GG) x := h1
    rw [h3, h2]
    rfl
  · intro h τ τ'
    rw [B.fields_emb_apply, B.fields_emb_apply, h τ, h τ']

theorem fields_ok : B.fields.Ok := by
  have hcm : IsCMField B.host.E := B.host.isCMField_hostE
  letI := B.host.cmStar
  have cm := host_cmData B.R B.host
  have hinj : ∀ {φ ψ : B.host.E →+* B.LL}, B.embLL.comp φ = B.embLL.comp ψ → φ = ψ := fun h =>
    RingHom.ext fun x => B.embLL.injective (RingHom.congr_fun h x)
  refine
    { realF := cm.totReal
      rankE := cm.deg2
      star_F := fun x => (cm.fixed _).2 ⟨x, rfl⟩
      conjE := fun φ x => ?_
      cplxE := inferInstanceAs (IsTotallyComplex B.host.E)
      emb_star := fun τ x => ?_
      card_Tau := ?_
      emb_inj := fun τ τ' h => ?_
      emb_ne := fun τ τ' h => ?_
      emb_all := fun φ => ?_
      cplxK := ?_
      normalK := inferInstanceAs (Normal ℚ B.LL)
      conjK := ⟨B.embLL, B.starLL_cx⟩
      quad := ?_ }
  · exact (congrArg φ (B.fields_star x)).trans (B.host.conjE_apply φ x)
  · apply B.embLL.injective
    rw [B.starLL_cx]
    exact (congrArg (B.embLL.comp (B.tauLL τ)) (B.fields_star x)).trans (B.host.conjE_apply (B.embLL.comp (B.tauLL τ)) x)
  · refine (card_Tau B.host).trans (Eq.trans ?_ (B.host.finrank_hostF).symm)
    rfl
  · have h1 := congrArg B.embLL.comp h
    rw [embLL_comp_emb, embLL_comp_emb] at h1
    exact Subtype.ext ((factEmb B.R B.host).1.1 h1)
  · have h1 := congrArg B.embLL.comp h
    rw [embLL_comp_emb, embLL_comp_embBar] at h1
    have h2 := (factEmb B.R B.host).1.1 h1
    exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 τ'.2 (h2 ▸ τ.2)
  · obtain ⟨g, hg⟩ := (factEmb B.R B.host).1.2 (B.embLL.comp φ)
    by_cases h : g ∈ B.R.Psi
    · exact ⟨⟨g, h⟩, Or.inl (hinj (by rw [← hg]; exact (embLL_comp_emb B ⟨g, h⟩).symm))⟩
    · have hcc : B.R.cc * B.R.cc = 1 := B.R.cc_mul_cc
      have h' : g * B.R.cc ∈ B.R.Psi := by
        rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem, mul_assoc, hcc, mul_one]
        exact h
      refine ⟨⟨_, h'⟩, Or.inr (hinj ?_)⟩
      rw [← hg, embLL_comp_embBar B ⟨_, h'⟩]
      show _ = B.host.emb (g * B.R.cc * B.R.cc)
      rw [mul_assoc, hcc, mul_one]
  · letI : Algebra B.host.E B.LL := B.embE.toAlgebra
    exact isTotallyComplex_of_algebra B.host.E B.LL
  · let e : B.fields.Kq ≃+* B.host.K :=
      RingEquiv.subringCongr (s := B.fields.Kq.toSubring) (t := B.host.K.toSubfield.toSubring)
        (Subring.ext fun x => mem_Kq_iff B x)
    rw [← SplitK.finrank_K B.host.hyp.2.1.pos B.host.sqrtMinusD_sq]
    exact (AlgEquiv.ofRingEquiv (R := ℚ) (f := e) (fun r => map_ratCast e r)).toLinearEquiv.finrank_eq

theorem fields_satisfy_definite_laws : ∀ B : Base, B.fields.AbelianUnramifiedExtensionConditions ∧ B.fields.f = B.R.f := by
  intro B
  refine ⟨⟨fields_ok B, ?_, B.host.hostE_isGalois, gal_comm B.host, unram B.host⟩, B.fields_f⟩
  rw [B.fields_f]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le B.host.two_le_e
  obtain ⟨m, hm⟩ := B.R.two_pow_dvd_ord
  refine ⟨2 ^ k * m, ?_⟩
  show 2 * B.R.ord = _
  rw [hm, hk]
  ring

end GlobalTheory.Mem.FieldsLaws
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem

theorem Base.fields_isCond : ∀ (B : Base) (X : PreX B.toPre), B.fields.IsCond (B.primes X).cond := by
  intro B X j
  exact UpperTheory.Ram.isCond_condN B.host j

end GlobalTheory.Mem
end

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_conjRows_eq {D : D7} (X : HidaSetting D) :
    Module.finrank ℂ (conjRows X) = Module.finrank ℂ (HHX X) := by
  let e := conjL (muX X)
  let j : conjRows X ≃+ HHX X :=
    { toFun := fun f => ⟨e f, f.2⟩
      invFun := fun g => ⟨e.symm g, by
        show e.toLinearEquiv.toLinearMap (e.symm g) ∈ HHX X
        simpa using g.2⟩
      left_inv := fun f => by ext1; simp
      right_inv := fun g => by ext1; simp
      map_add' := fun f g => by ext1; simp }
  have hbij : Function.Bijective (starRingEnd ℂ : ℂ → ℂ) :=
    Function.Involutive.bijective (fun z => by simp)
  have hr := rank_eq_of_equiv_equiv (starRingEnd ℂ : ℂ → ℂ) j hbij (fun r m => by
    ext1
    show e (r • (m : L2X X)) = (starRingEnd ℂ r) • e m
    exact e.map_smulₛₗ r m)
  unfold Module.finrank
  rw [hr]

theorem exists_rowJ_and_finrank_HHX : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), 0 < c → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → R.models_HE → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → (R.EEat (R.levR F true) ≤ R.EEat R.triv) → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) → (DallTie R F → Module.finrank ℂ (HHX X) = D.what₂.Dall) ∧ ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h G t v₀ c eE hc hv₀ hE hrange hnorm hle hJ1 hJ2
  refine ⟨fun hD => ?_, exists_rowJ_of_evalOn hc hv₀ hE hrange hnorm hle hJ2⟩
  obtain ⟨J1, -⟩ := hJ1
  have hD' : D.what₂.Dall = Module.finrank ℂ (MultR R F) := hD
  rw [hD', J1.finrank_eq, finrank_conjRows_eq]

end GlobalTheory.Mem.SRe

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.TorsionDegree

theorem exists_torsion_param_lattice (L : PeriodPair) (n : ℕ) [NeZero n] :
    ∃ t : (Fin 2 → ZMod n) →+ (latticeCurve L).toAffine.Point, Function.Injective t ∧
      ∀ P, n • P = 0 → ∃ v, t v = P := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let f : ℂ → ℤ →+ (latticeCurve L).toAffine.Point := fun ω =>
    (latticePointHom L).comp (zmultiplesHom ℂ (ω / n))
  have hf : ∀ ω (a : ℤ), f ω a = latticePoint L (a * (ω / n)) := fun ω a => by
    simp [f]
  have h0 : ∀ ω ∈ L.lattice, f ω n = 0 := fun ω hω => by
    rw [hf, latticePoint_eq_zero_iff]
    convert hω using 1
    push_cast
    field_simp
  let t : (Fin 2 → ZMod n) →+ (latticeCurve L).toAffine.Point :=
    (ZMod.lift n ⟨f L.ω₁, h0 _ L.ω₁_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 0) +
    (ZMod.lift n ⟨f L.ω₂, h0 _ L.ω₂_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 1)
  have ht : ∀ a b : ℤ, t ![(a : ZMod n), (b : ZMod n)] = latticePoint L ((a * L.ω₁ + b * L.ω₂) / n) := by
    intro a b
    simp only [t, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, ZMod.lift_coe, hf]
    rw [← latticePoint_add]
    congr 1
    ring
  refine ⟨t, (injective_iff_map_eq_zero t).2 fun v hv => ?_, fun P hP => ?_⟩
  · obtain ⟨a, ha⟩ := ZMod.intCast_surjective (v 0)
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (v 1)
    have e : v = ![(a : ZMod n), (b : ZMod n)] := by
      ext i; fin_cases i <;> simp [ha, hb]
    rw [e, ht, latticePoint_eq_zero_iff, PeriodPair.mem_lattice] at hv
    obtain ⟨c, d, hcd⟩ := hv
    have h1 : ((a - n * c : ℤ) : ℝ) • L.ω₁ + ((b - n * d : ℤ) : ℝ) • L.ω₂ = 0 := by
      rw [eq_div_iff hn'] at hcd
      simp only [Complex.real_smul]
      push_cast
      linear_combination -hcd
    obtain ⟨h2, h3⟩ := LinearIndependent.pair_iff.1 L.indep _ _ h1
    have h2' : a = n * c := by
      have : a - n * c = 0 := by exact_mod_cast h2
      omega
    have h3' : b = n * d := by
      have : b - n * d = 0 := by exact_mod_cast h3
      omega
    rw [e, h2', h3']
    ext i; fin_cases i <;> simp
  · obtain ⟨z, rfl⟩ := latticePoint_surjective L P
    have h1 : latticePoint L (n • z) = 0 := by
      rw [← latticePointHom_apply, map_nsmul, latticePointHom_apply]; exact hP
    rw [latticePoint_eq_zero_iff] at h1
    obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 h1
    refine ⟨_, (ht a b).trans ?_⟩
    rw [hab, nsmul_eq_mul, mul_div_cancel_left₀ _ hn']

theorem exists_torsion_param (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ) [NeZero n] :
    ∃ t : (Fin 2 → ZMod n) →+ W.toAffine.Point, Function.Injective t ∧
      ∀ P, n • P = 0 → ∃ v, t v = P := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve W
  let e := variableChangePointEquiv C hC
  obtain ⟨t, hi, hs⟩ := exists_torsion_param_lattice L n
  refine ⟨e.toAddMonoidHom.comp t, e.injective.comp hi, fun P hP => ?_⟩
  obtain ⟨v, hv⟩ := hs (e.symm P) (by rw [← map_nsmul, hP, map_zero])
  exact ⟨v, by simp [hv]⟩

theorem exists_linearEquiv {G G' : Type} [AddCommGroup G] [AddCommGroup G'] (n : ℕ) [NeZero n]
    (t : (Fin 2 → ZMod n) →+ G') (hi : Function.Injective t) (hs : ∀ P, n • P = 0 → ∃ v, t v = P)
    (ι φ : G →+ G') (hι : Function.Injective ι) (hφ : Function.Injective φ)
    (hr : ∀ P, n • P = 0 → ∃ Q, ι Q = P) :
    ∃ g : (Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n), ∀ v Q, ι Q = t v → φ Q = t (g v) := by
  have hv : ∀ v : Fin 2 → ZMod n, n • v = 0 := fun v => by
    ext i; simp
  have h1 : ∀ v, ∃ Q, ι Q = t v := fun v => hr _ (by rw [← map_nsmul, hv, map_zero])
  choose s hs' using h1
  have h2 : ∀ v, ∃ w, t w = φ (s v) := fun v => hs _ (by
    have : n • s v = 0 := hι (by rw [map_nsmul, hs', ← map_nsmul, hv, map_zero, map_zero])
    rw [← map_nsmul, this, map_zero])
  choose u hu using h2
  have hadd : ∀ v w, u (v + w) = u v + u w := fun v w => hi (by
    rw [map_add (f := _), hu, hu, hu, ← map_add (f := _)]
    congr 1
    exact hι (by rw [map_add (f := _), hs', hs', hs', map_add (f := _)]))
  let U := (AddMonoidHom.mk' u hadd).toZModLinearMap n
  have hU : Function.Injective U := fun v w h => hi (by
    have h' : u v = u w := h
    rw [← hs', ← hs', hφ ((hu v).symm.trans (h' ▸ hu w))])
  refine ⟨LinearEquiv.ofBijective U ⟨hU, Finite.surjective_of_injective hU⟩, fun v Q hQ => ?_⟩
  rw [hι (hQ.trans (hs' v).symm), ← hu]
  rfl

theorem card_linearEquiv (n : ℕ) :
    Nat.card ((Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)) = Nat.card (GL (Fin 2) (ZMod n)) :=
  Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).symm.toEquiv

theorem finrank_adjoin_le {k : Type} [Field k] [CharZero k] [Algebra k ℂ] (A : WeierstrassCurve k) [A.IsElliptic]
    (n : ℕ) [NeZero n] [FiniteDimensional k (IntermediateField.adjoin k (torsionCoords (A.baseChange ℂ) n))] :
    Module.finrank k (IntermediateField.adjoin k (torsionCoords (A.baseChange ℂ) n)) ≤
      Nat.card (GL (Fin 2) (ZMod n)) := by
  classical
  set S := torsionCoords (A.baseChange ℂ) n with hS
  set M := IntermediateField.adjoin k S with hM
  have : (A.baseChange ℂ).IsElliptic := inferInstanceAs (A.map _).IsElliptic
  obtain ⟨t, hi, hs⟩ := exists_torsion_param (A.baseChange ℂ) n
  let m : (M →ₐ[k] ℂ) → (A.baseChange M).toAffine.Point →+ (A.baseChange ℂ).toAffine.Point :=
    fun φ => WeierstrassCurve.Affine.Point.map (W' := A.toAffine) φ
  have hm : ∀ φ, Function.Injective (m φ) := fun φ => WeierstrassCurve.Affine.Point.map_injective φ
  have hpt : ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y) (hx : x ∈ M) (hy : y ∈ M),
      (A.baseChange M).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ := fun x y h hx hy =>
    (A.toAffine.baseChange_nonsingular (f := M.val) M.val.injective ⟨x, hx⟩ ⟨y, hy⟩).mp h
  have hr : ∀ P, n • P = 0 → ∃ Q, m M.val Q = P := by
    rintro (_ | ⟨x, y, h⟩) hP
    · exact ⟨0, rfl⟩
    · exact ⟨.some _ _ (hpt x y h (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inl rfl⟩)
        (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inr rfl⟩)), rfl⟩
  choose g hg using fun φ => exists_linearEquiv n t hi hs (m M.val) (m φ) (hm _) (hm φ) hr
  have hginj : Function.Injective g := by
    intro φ ψ h
    refine IntermediateField.algHom_ext_of_eq_adjoin k hM ?_
    rintro z ⟨x, y, hxy, h0, hz⟩
    obtain ⟨v, hv⟩ := hs _ h0
    have hx := IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inl rfl⟩
    have hy := IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inr rfl⟩
    have e : m φ (.some _ _ (hpt x y hxy hx hy)) = m ψ (.some _ _ (hpt x y hxy hx hy)) := by
      rw [hg φ v _ hv.symm, hg ψ v _ hv.symm, h]
    have e' := WeierstrassCurve.Affine.Point.some.inj e
    rcases hz with rfl | rfl
    · exact e'.1
    · exact e'.2
  rw [← card_linearEquiv, ← AlgHom.card k M ℂ, ← Nat.card_eq_fintype_card]
  have : Finite ((Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := (Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)))
  exact Nat.card_le_card_of_injective g hginj

theorem finrank_sup_adjoin {K L : Type} [Field K] [Field L] [Algebra K L] (H : IntermediateField K L) (S : Set L)
    [FiniteDimensional K H] [FiniteDimensional H (IntermediateField.adjoin H S)] :
    FiniteDimensional K (H ⊔ IntermediateField.adjoin K S : IntermediateField K L) ∧
      Module.finrank K (H ⊔ IntermediateField.adjoin K S : IntermediateField K L) =
        Module.finrank K H * Module.finrank H (IntermediateField.adjoin H S) := by
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup]
  have : IsScalarTower K H (IntermediateField.adjoin H S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Free H (IntermediateField.adjoin H S) := Module.Free.of_divisionRing _ _
  have : Module.Free K H := Module.Free.of_divisionRing _ _
  have h : FiniteDimensional K (IntermediateField.adjoin H S) := Module.Finite.trans H _
  exact ⟨h,
    (Module.finrank_mul_finrank K H (IntermediateField.adjoin H S)).symm⟩

theorem finrank_torsionField_le : ∀ (d : ℕ) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (A : WeierstrassCurve F) [A.IsElliptic], FiniteDimensional ℚ (torsionField d A) ∧ Module.finrank ℚ (torsionField d A) ≤ Module.finrank ℚ (hilbertField d F) * Nat.card (GL (Fin 2) (ZMod 12)) := by
  intro d F _ A _
  have hint : IsIntegral ℚ (sqrtNegNat d) :=
    IsIntegral.of_pow (n := 2) (by norm_num) (by
      rw [sqrtNegNat_sq]
      exact (isIntegral_natCast d).neg)
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat d⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hH : FiniteDimensional ℚ (hilbertField d F) := by
    unfold hilbertField; infer_instance
  set H := hilbertField d F with hHdef
  let A' : WeierstrassCurve H := A.map (IntermediateField.inclusion (le_sup_right : F ≤ H)).toRingHom
  have hA : A'.baseChange ℂ = A.baseChange ℂ := by
    simp only [A', WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    rfl
  have : (A.baseChange ℂ).IsElliptic := inferInstanceAs (A.map _).IsElliptic
  have : A'.IsElliptic := by
    simp only [A']
    exact WeierstrassCurve.instIsEllipticMap _ _
  have hfin := finite_torsionCoords (A.baseChange ℂ) 12 (by norm_num)
  have halg := FieldsEx.isAlgebraic_of_torsionCoords_finite F A 12 hfin
  have : Finite (torsionCoords (A'.baseChange ℂ) 12) := hA ▸ hfin.to_subtype
  have hM : FiniteDimensional H (IntermediateField.adjoin H (torsionCoords (A'.baseChange ℂ) 12)) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (halg z (hA ▸ hz)).isIntegral.tower_top
  have hle := finrank_adjoin_le A' 12
  obtain ⟨h1, h2⟩ := finrank_sup_adjoin H (torsionCoords (A'.baseChange ℂ) 12)
  have e : torsionField d A = H ⊔ IntermediateField.adjoin ℚ (torsionCoords (A'.baseChange ℂ) 12) := by
    rw [hA]
    rfl
  rw [e]
  exact ⟨h1, h2.le.trans (Nat.mul_le_mul_left _ hle)⟩

end GlobalTheory.Mem.TorsionDegree
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.rayClassField_finrank_pow_principal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)), IsRayField K L 𝔮 → ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 → ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I ^ Module.finrank K L * Ideal.span {β} = Ideal.span {α} := by
  first | exact @GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal | exact GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal | (intros; apply GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.classNumber_dvd_finrank_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → IsRayField K L 𝔮 → classNumber K ∣ Module.finrank K L := by
  first | exact @GlobalTheory.Mem.ClassDvd.classNumber_dvd_finrank | exact GlobalTheory.Mem.ClassDvd.classNumber_dvd_finrank | (intros; apply GlobalTheory.Mem.ClassDvd.classNumber_dvd_finrank <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.finiteDimensional_kummerFieldOfPowerIdealRoots : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ), h ≠ 0 → FiniteDimensional ℚ (kummerField φ h) := by
  first | exact @GlobalTheory.Mem.FieldsEx.finiteDimensional_kummerField | exact GlobalTheory.Mem.FieldsEx.finiteDimensional_kummerField | (intros; apply GlobalTheory.Mem.FieldsEx.finiteDimensional_kummerField <;> assumption)
end
