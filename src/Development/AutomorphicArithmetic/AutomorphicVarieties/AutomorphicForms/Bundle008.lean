module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle382
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle296
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle274
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemFiniteCocyclesIffBcrisTensorCoboundary

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open TensorProduct Module GlobalTheory.CoeffExt
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.ExLib

theorem eventually_sat (hS : SatLoc) {F : Type} [Field F] [NumberField F] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Af F)) V) (hρ : GlobalTheory.PRep.IsSmooth ρ) (h : ∀ w, ∃ σ, LocIsotypic ρ w σ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine .of_forall fun w => ?_
    obtain ⟨σ, hσ, -⟩ := h w
    exact absurd hσ (not_nontrivial V)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨S, hU⟩ := GlobalFixedVectors.exists_KAway_subset (M := 1) ((hρ v).mem_nhds (by simp))
  filter_upwards [S.eventually_cofinite_notMem] with w hw
  obtain ⟨σ, hi⟩ := h w
  obtain ⟨h1, h2⟩ := hS F n w σ
  have hK : IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GL (Fin n) (w.adicCompletion F))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F w)
  have h0 : ((1 : ℕ) : 𝓞 F) ∉ w.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top
  obtain ⟨B, hB⟩ := h1 (hasFixed_of_sum σ.ρ σ.smooth (ρ.comp (locGL F n w)) _ hK hi.2
    ⟨v, hv, fun u hu => hU (GlobalFixedVectors.mem_KAway.2 ⟨locGL_mem_KLev n w h0 hu, fun x hx =>
      pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _⟩)⟩)
  exact ⟨B, (h2 _ _ hi B).2 hB⟩

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  {V' : Type} [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
  [Module ↥L'.1 V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[↥L.1] (ι → V)}

theorem isSst_iff : IsSst P ρ ↔ finrank ℚ_[l] ↥(Dst P ρ) = finrank ℚ_[l] ↥(K0 K) * finrank ℚ_[l] V := by
  have := L.2
  rw [IsSst, ← finrank_mul_finrank ℚ_[l] ↥L.1 V, ← finrank_mul_finrank ℚ_[l] ↥L.1 ↥(Dst P ρ), mul_left_comm]
  exact (Nat.mul_right_inj finrank_pos.ne').symm

private theorem finrank_fun' {k M ι : Type} [Field k] [AddCommGroup M] [Module k M] [Fintype ι] :
    finrank k (ι → M) = Fintype.card ι * finrank k M := by
  rw [finrank, rank_fun, Cardinal.toNat_mul, Cardinal.toNat_natCast, finrank]

theorem isSst_of_coord (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (h : IsSst P ρ) : IsSst P ρ' := by
  have hm : ∀ x : V' ⊗[ℚ_[l]] Bst P, x ∈ Dst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dst P ρ := fun x => by
    simp only [mem_Dst]
    refine ⟨fun hx i g => by rw [← GlobalTheory.PstExt.tensCoord_stRep P hE, hx g], fun hx g => ?_⟩
    exact (tensCoord E (Bst P)).injective (funext fun i => by rw [GlobalTheory.PstExt.tensCoord_stRep P hE, hx i g])
  let e : ↥(Dst P ρ') ≃ₗ[ℚ_[l]] (ι → ↥(Dst P ρ)) :=
    { toFun := fun x i => ⟨tensCoord E (Bst P) x.1 i, (hm _).1 x.2 i⟩
      invFun := fun y => ⟨(tensCoord E (Bst P)).symm fun i => (y i).1, (hm _).2 fun i => by
        rw [LinearEquiv.apply_symm_apply]; exact (y i).2⟩
      map_add' := fun x y => funext fun i => Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
      map_smul' := fun c x => funext fun i =>
        Subtype.ext (congrFun (((tensCoord E (Bst P)).restrictScalars ℚ_[l]).map_smul c x.1) i)
      left_inv := fun x => Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
      right_inv := fun y => funext fun i =>
        Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i) }
  rw [isSst_iff] at h ⊢
  rw [e.finrank_eq, (E.restrictScalars ℚ_[l]).finrank_eq, finrank_fun', finrank_fun', h, mul_left_comm]

end Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {m : ℕ}

theorem isSst_enlarge {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1)
    (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1) (h : IsSst P (Bw.repE L₁ r₁)) :
    IsSst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isSst_of_coord P (E := vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

theorem isSstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsSstAt P Bw r) : IsSstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  refine ⟨L₂, r₂, hm, isSst_of_coord P (ι := Unit) (E := e.symm.trans (LinearEquiv.funUnique Unit _ _).symm)
    (fun g x _ => ?_) (isSst_enlarge P Bw hL r₁ hp)⟩
  change e.symm _ = Bw.repE L₂ _ g (e.symm x)
  rw [e.symm_apply_eq, he, e.apply_symm_apply]

theorem isPstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsPstAt P Bw r) : IsPstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  exact ⟨L₂, r₂, hm, GlobalTheory.PstConj.isPst_congr P e he (GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hp)⟩

theorem wdAt_conj [NumberField E] [IsAlgClosure E Ω] (ι : Om l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (hj : Induces Bw)
    {r r' : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A) →* GL (Fin m) (Om l)} (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) :
    wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  by_cases hr : IsPstAt P Bw r
  · exact GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj r r' p hc hr (isPstAt_conj P Bw p hc hr)
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, wdAt_of_not_isPstAt ι Bw h hj fun hr' =>
      hr (isPstAt_conj P Bw p⁻¹ (fun g => by rw [hc]; group) hr')]

theorem isConjDual_of_iso {k : Type} [Field k] {c : Ω ≃+* Ω} {r r' : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin m) k} {μ : _root_.Formalism.ConjugateSelfDual.G E Ω →* kˣ}
    (H : IsConjDual c r μ) (h : RepIso r r') : IsConjDual c r' μ := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨Q, hQ⟩ := H
  let t : GL (Fin m) k := ⟨(g : Matrix (Fin m) (Fin m) k)ᵀ, ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)ᵀ,
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩
  have ht : (t : Matrix (Fin m) (Fin m) k) = (g : Matrix (Fin m) (Fin m) k)ᵀ := rfl
  have ht' : ((t⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)ᵀ := rfl
  refine ⟨g * Q * t, fun s s' hs => ?_⟩
  rw [hg s', hg s⁻¹]
  simp only [Units.val_mul, mul_inv_rev, hQ s s' hs, Matrix.transpose_mul, ← ht, ← ht', Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem isGalRepOf_of_iso [NumberField E] [IsAlgClosure E Ω] [IsCMField E] {π : CuspSub E m}
    {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r r' : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin m) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : IsGalRepOf π χ ι r wt HT) (hs : IsSSRep r') (h : RepIso r r') :
    IsGalRepOf π χ ι r' wt HT := by
  obtain ⟨μ, h1, h2⟩ := H.pol
  have hc := continuous_of_iso H.cont h
  have h3 := fun c hc => isConjDual_of_iso (h2 c hc) h
  obtain ⟨g, hg⟩ := h
  have hg' : ∀ s, g * r s = r' s * g := fun s => by rw [hg, inv_mul_cancel_right]
  refine ⟨hc, hs, ⟨μ, h1, h3⟩, fun w hw A h rc hrc σ hσ => (H.away w hw A h rc hrc σ hσ).of_conj hw g fun s => hg' _,
    fun w hw A h => (H.pure w hw A h).imp fun x hx => ⟨hx.1.of_conj hw g fun s => hg' _, hx.2⟩, H.weights, H.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj => ?_⟩
  have Ha := H.above P AI T w A h O Bw hj
  have e : ∀ s : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A), r'.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype s = g * r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype s * g⁻¹ :=
    fun s => hg s
  obtain ⟨c1, c2, -, c4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l P E Ω O _ Bw m _ _ g e
  exact ⟨c1 Ha.deRham, fun τ L τ' hτ => c4 _ _ (Ha.jumps τ L τ' hτ), fun σ hσ hf =>
    ⟨isSstAt_conj P Bw g e (Ha.iwahori σ hσ hf).1, fun rc hrc =>
      (wdAt_conj P ι Bw h hj g e).trans ((Ha.iwahori σ hσ hf).2 rc hrc)⟩, fun σ hσ hf => c2 (Ha.crys σ hσ hf)⟩

end UpperTheory.V.Af.ExLib

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.Gu

section Defs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]


variable (Ω) in
abbrev Par (w : HeightOneSpectrum (𝓞 E)) : Type 1 :=
  ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w), (IrrGL (k := w.adicCompletion E) → WD h) → WD h

abbrev cl {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : IrrGL (k := w.adicCompletion E) :=
  IrrGL.of σ.ρ σ.smooth σ.irred

def ParAt {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (p : Par Ω w) : Prop :=
  ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
    (((l : ℕ) : 𝓞 E) ∉ w.asIdeal → Lev.WO ι r (p A h rc)) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
        Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)) (p A h rc)

theorem locGlob_iff {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) : LocGlob ι r w σ ↔ ParAt ι r w fun _ _ rc => rc (algNorm σ) := Iff.rfl

theorem ParAt.congr {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 E)} {p p' : Par Ω w}
    (H : ParAt ι r w p) (e : ∀ A h rc, IsRec h rc → p A h rc = p' A h rc) : ParAt ι r w p' :=
  fun A h rc hrc => e A h rc hrc ▸ H A h rc hrc

structure Compat {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)) (p : ∀ w : HeightOneSpectrum (𝓞 E), Par Ω w)
    (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  ht : HasHT r HT
  par : ∀ w, ParAt ι r w (p w)

def ex (n d k : ℕ) : ℤ := (d : ℤ) - 2 * k - n

def totPar (n : ℕ) {c : ℕ} {a : Fin c → ℕ} (d : Fin c → ℕ) {w : HeightOneSpectrum (𝓞 E)}
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) : Par Ω w := fun _ _ rc =>
  sumList (List.ofFn fun i => sumList (List.ofFn fun k : Fin (d i) => (rc (cl (ρ i))).lpTw ((ex n (d i) k : ℝ) / 2)))

def satTot (w : HeightOneSpectrum (𝓞 E)) {c : ℕ} (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ) : Multiset ℂˣ :=
  ∑ i, ∑ k : Fin (d i), (S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2))

end Defs

def SumAway : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a b : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (r' : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin b) (Qbar l)), Continuous r → Continuous r' →
    ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (x x' : WD h),
      IsWDOf ι r x → IsWDOf ι r' x' → IsWDOf ι (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (x.lpSum x')

def SumHT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (a b : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (r' : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin b) (Qbar l)), Continuous r → Continuous r' →
    ∀ HT HT', HasHT r HT → HasHT r' HT' → HasHT (Formalism.MainNotions.SumRepresentations.At.sumRep r r') fun τ => HT τ + HT' τ

def SumTwo : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a b : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (r' : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin b) (Qbar l)) p p' HT HT',
    Compat ι r p HT → Compat ι r' p' HT' →
      Compat ι (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (fun w A h rc => (p w A h rc).lpSum (p' w A h rc)) fun τ => HT τ + HT' τ

def SumRed : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a b : ℕ) (r : Γ →* GL (Fin a) k) (r' : Γ →* GL (Fin b) k), 1 ≤ a → 1 ≤ b →
    ¬ IsIrr (Formalism.MainNotions.SumRepresentations.At.sumRep r r')

def SumFam : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (c : ℕ), 1 ≤ c → ∀ (N : Fin c → ℕ), (∀ i, 1 ≤ N i) → ∀ (n : ℕ), ∑ i, N i = n →
    ∀ (r : ∀ i, _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin (N i)) (Qbar l)) (p : Fin c → ∀ w : HeightOneSpectrum (𝓞 E), Par Ω w)
      (HT : Fin c → (E →+* Qbar l) → Multiset ℤ), (∀ i, Compat ι (r i) (p i) (HT i)) →
      ∃ R : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l),
        Compat ι R (fun w A h rc => sumList (List.ofFn fun i => p i w A h rc)) (fun τ => ∑ i, HT i τ) ∧
        (IsIrr R → c = 1 ∧ ∀ i, IsIrr (r i))

def Eta : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (f : ℤ), ∃ (ξ : HChar E) (m : (E →+* ℂ) → ℤ), ξ.IsAlg m ∧
    compNorm E (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2) * ξ)) = 1

def TwistLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (P : CuspSub E a) (t : ℝ) (w : HeightOneSpectrum (𝓞 E))
    (ρ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w ρ →
      ∃ σ, (P.twist (GlobalTheory.HeckeGal.Model.absPow E t)).IsLocComp w σ ∧ cl σ = (cl ρ).nu (t : ℂ)

def CompatPol : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (P : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ξ : HChar E) (m : (E →+* ℂ) → ℤ),
    (CG.mk P).IsRegAlg → IsPolarized P χ → ξ.IsAlg m → GlobalTheory.ContraPair.DualIsConj (P.twist ξ) →
    ∀ σ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin a) (w.adicCompletion E)), (∀ w, P.IsLocComp w (σ w)) →
      ∃ (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (HT : (E →+* Qbar l) → Multiset ℤ),
        Compat ι r (fun w _ _ rc => rc (algNorm (σ w))) HT ∧
        ∀ τ : E →+* Qbar l, (HT τ).map (fun k : ℤ => (k : ℂ)) =
          ((CG.mk P).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z

def Half : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (P : CuspSub E a), P.IsCsd →
    ∀ (ρ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin a) (w.adicCompletion E))), (∀ w, P.IsLocComp w (ρ w)) →
    ∀ (m : (E →+* ℂ) → Multiset ℂ), (∀ τ, P.HasInfChar τ (m τ)) → ∀ e : ℤ,
      (∀ τ, (m τ).Nodup ∧ ∀ z ∈ m τ, ∃ j : ℤ, z + (e : ℂ) / 2 = j) →
      ∃ (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (HT : (E →+* Qbar l) → Multiset ℤ),
        Compat ι r (fun w _ _ rc => (rc (cl (ρ w))).lpTw ((e : ℝ) / 2)) HT ∧
        ∀ τ : E →+* Qbar l, (HT τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map fun z => -(z + (e : ℂ) / 2)

def Strings : Prop :=
  ∀ (n c : ℕ) (d : Fin c → ℕ) (m : Fin c → Multiset ℂ) (lam : DomWeight n),
    ∑ i, GlobalTheory.DefiniteBC.spehInf (d i) (m i) = infOfWeight lam →
    (∀ i (k : Fin (d i)), (m i).Nodup ∧ ∀ z ∈ m i, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j) ∧
      ∑ i, ∑ k : Fin (d i), (m i).map (fun z => -(z + (ex n (d i) k : ℂ) / 2)) =
        (infOfWeight lam).map fun z => ((n : ℂ) - 1) / 2 - z

def CompUnique : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (ρ₁ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ₂ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₁ →
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₂ → Nonempty (ρ₁.Equiv ρ₂)

def RecTot : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (n c : ℕ) (a d : Fin c → ℕ) (hn : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (w : HeightOneSpectrum (𝓞 E))
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (σ : ∀ i, SmIrr (GL (Fin (d i * a i)) (w.adicCompletion E))),
    (∀ i, 1 ≤ a i ∧ 1 ≤ d i) → (∀ i, (P i).IsLocComp w (ρ i)) →
    (∀ i, GlobalTheory.SmGL.IsUnitarisable (ρ i).ρ ∧ GlobalTheory.SmGL.IsUnitarisable (σ i).ρ ∧ IsSpeh (cl (ρ i)) (d i) (σ i).ρ) →
    ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), Nonempty (τ.ρ.Equiv (locProd hn w σ)) →
    ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
      totPar n d ρ A h rc = rc (algNorm τ)

def FrobTot : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n c : ℕ) (a d : Fin c → ℕ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (S : Fin c → Multiset ℂˣ), (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) →
      ParAt ι r w (totPar n d ρ) → FrobEig ι r w (algSat n (normV w) (satTot w d S))

def PolOfFrob : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)), Continuous r → IsSSRep r →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : Multiset ℂˣ,
      FrobEig ι r w (algSat n (normV w) (B.map (·⁻¹))) ∧ FrobEig ι r (Bc.cPl w) (algSat n (normV (Bc.cPl w)) B)) →
    ∀ c : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield E) Ω, IsConjEl c → ∃ P, IsPairing c r (cycBar E Ω l ^ (1 - (n : ℤ))) P

def SatLink : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (P : CuspSub E a),
    (∀ (w : HeightOneSpectrum (𝓞 E)) (ρ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w ρ →
      ∀ B, (CG.mk P).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w ρ.ρ B) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk P).HasSat w B

def SatConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    (∀ (a : ℕ) (P : CuspSub E a), P.IsCsd → ∀ B, (CG.mk P).HasSat (Bc.cPl w) B → (CG.mk P).HasSat w (B.map (·⁻¹))) ∧
    ∀ (c : ℕ) (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ),
      satTot w d (fun i => (S i).map (·⁻¹)) = (satTot (Bc.cPl w) d S).map (·⁻¹)

def IrrCase : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ (c : ℕ) (a d : Fin c → ℕ) (hn : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
      (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (m : Fin c → (E →+* ℂ) → Multiset ℂ),
      GlobalTheory.BcSpeh.Parts π a d hn P ρ m → c = 1 → (∀ i, d i = 1) → ∀ r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l), IsSSRep r →
      (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ S : Fin c → Multiset ℂˣ, (∀ i, (CG.mk (P i)).HasSat w (S i)) ∧
        FrobEig ι r w (algSat n (normV w) (satTot w d S))) →
      ∃ Q : CuspSub E n, (CG.mk Q).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj Q ∧ AttC ι r Q ∧
        ∀ φ lam, HasWeightAt π φ lam → Q.HasInfChar φ (infOfWeight lam)

end UpperTheory.V.Af.Gu
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

theorem UpperTheory.V.Af.Bc.bcAtt : BcAtt := UpperTheory.baseChange_attached_of_frobenius_restriction UpperTheory.frobenius_power_compatibility

theorem UpperTheory.V.Af.Bc.irrBasic : IrrBasic := UpperTheory.galoisRep_irreducibility_criterion

theorem UpperTheory.V.Af.Bc.noTwist (hP : Hypotheses₂) : NoTwist :=
  UpperTheory.baseChange_noSelfTwist_of_frobenius_sign_irreducible (isoOfFrob hP) UpperTheory.frobenius_eigenvalues_twist UpperTheory.exists_quadratic_sign_character UpperTheory.frobenius_sign_compatibility UpperTheory.schur_twist_holds UpperTheory.galoisRep_irreducibility_criterion

theorem UpperTheory.V.Af.Bc.normGal : NormGal := UpperTheory.galois_norm_compatibility_of_frobenius_restriction UpperTheory.frobenius_power_compatibility (UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility)
end
