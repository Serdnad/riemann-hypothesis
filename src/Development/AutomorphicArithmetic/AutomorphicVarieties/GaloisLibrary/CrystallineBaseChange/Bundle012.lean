module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br

def SelfIso : Prop :=
  StrongMultOneReal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (η : HChar F),
    η ^ 2 = 1 → SelfTw π.HasSat η → IsoTwist π η

def BcAtt0 : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC0 π P →
      (π.IsRegAlg → (CG.mk P).IsRegAlg) ∧ (AttR ι r π → IsSSRep (r.comp (Bc.res F Ω E)) → AttC ι (r.comp (Bc.res F Ω E)) P)

def BcConj0 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
    (n : ℕ) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC0 π P →
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat (Bc.cPl w) B

def BcDual0 : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual →
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ (n : ℕ), 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F) (P : CuspSub K n), π.Polarized χ → IsBC0 π P →
    ∃ χ' : HChar (maximalRealSubfield K), (∀ v v' : InfinitePlace (maximalRealSubfield K), χ'.locInf v (-1) = χ'.locInf v' (-1)) ∧
      GlobalTheory.ContraPair.DualIsConjBy P (compNorm K χ')

def PlaceOf : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (i : v.adicCompletion F ≃+* w.adicCompletion K), Continuous i →
    (∀ x : F, i (algebraMap F _ x) = algebraMap K _ (algebraMap F K x)) →
    w.under (𝓞 F) = v ∧ ∃ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w ∧
      PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i

def WdAway : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i →
    ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)),
    ∀ (x : WD h) (y : WD h'), IsWDOf ι r x → IsWDOf ι (r.comp (Bc.res F Ω K)) y → WDRel (RingEquiv.refl Ω) x y

def RecInv : Prop :=
  GlobalTheory.Published.LocalLanglandsGL → ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω]
    [IsAlgClosure F Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K),
    PlaceIso A v A w (RingEquiv.refl Ω) j i → ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (v.adicCompletion F)))
    (σ' : SmIrr (GL (Fin n) (w.adicCompletion K))) rc rc', IsRec h rc → IsRec h' rc' →
    WDRel (RingEquiv.refl Ω) (rc (algNorm σ)) (rc' (algNorm σ')) →
    ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)

def SplitOf : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ExC → ExR →
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F) (P : CuspSub K n), π.IsRegAlg → π.Polarized χ →
      IsBC0 π P → SplitIso π P

end UpperTheory.V.Br
end
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

theorem UpperTheory.V.Br.potMove :
    UpperTheory.V.Br.PotMove := by
  intro F Ω _ _ _ _ _ l _ n r A A' g hg hA
  obtain ⟨O, i1, i2, i3, Bw, hj, LL', r', ⟨hle, hmap⟩, K', hK', hcr⟩ := hA
  have hmem : ∀ s : G F Ω, s ∈ Dec (F := F) A' ↔ g * s * g⁻¹ ∈ Dec (F := F) A := fun s => by
    have hgA : g • A' = A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hg]
      simp [AlgEquiv.smul_def]
    rw [mem_Dec, mem_Dec, ← hgA, mul_smul, inv_smul_smul, mul_smul, smul_left_cancel_iff]
  let φ : ↥(Dec (F := F) A') ≃* ↥(Dec (F := F) A) :=
    { toFun := fun s => ⟨g * s * g⁻¹, (hmem s).1 s.2⟩
      invFun := fun t => ⟨g⁻¹ * t * g, (hmem _).2 (by
        have e : g * (g⁻¹ * (t : G F Ω) * g) * g⁻¹ = t := by group
        rw [e]; exact t.2)⟩
      left_inv := fun s => Subtype.ext (by dsimp only; group)
      right_inv := fun t => Subtype.ext (by dsimp only; group)
      map_mul' := fun s t => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : Continuous φ :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hφs : Continuous φ.symm :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hjE : ∀ x : F, Bw.j (g (algebraMap F Ω x)) = Bw.j (algebraMap F Ω x) := fun x => by
    rw [AlgEquiv.commutes]
  let Bw' : LocBridge l F Ω (Dec (F := F) A') O :=
    { Kw := Bw.Kw, j := Bw.j.comp (g : Ω →+* Ω)
      j_E := fun x => by
        change Bw.j (g (algebraMap F Ω x)) ∈ _
        rw [hjE]; exact Bw.j_E x
      j_dense := Bw.j_dense.trans (closure_mono (by
        rintro _ ⟨x, rfl⟩
        exact ⟨x, hjE x⟩))
      e := φ.trans Bw.e
      e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
      e_comm := fun s x => by
        refine (Bw.e_comm (φ s) (g x)).trans ?_
        change Bw.j ((g * (s : G F Ω) * g⁻¹) (g x)) = Bw.j (g ((s : G F Ω) x))
        simp
      LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }
  have h1 : PotCrysAt (r.comp (MulAut.conj g).toMonoidHom) A' := by
    refine ⟨O, i1, i2, i3, Bw', fun x => (hg x).trans (hj (g x)), LL', r'.comp φ.toMonoidHom,
      ⟨hle, MonoidHom.ext fun s => DFunLike.congr_fun hmap (φ s)⟩, K', hK', ?_⟩
    have e : Bw'.repE LL' (r'.comp φ.toMonoidHom) = Bw.repE LL' r' := by
      refine MonoidHom.ext fun t => ?_
      simp [LocBridge.repE, Bw']
    rw [e]
    exact hcr
  refine h1.of_iso ⟨(r g)⁻¹, fun s => ?_⟩
  simp [mul_assoc]
end
