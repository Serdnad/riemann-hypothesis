module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle327
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle170
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.exists_ccr_operators_thetaFunctions : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D), ∃ x d : GlobalTheory.RealWeil.Ix S T → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), IsCCR x d ∧ ∀ (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (f : GlobalTheory.RealWeil.thetaSub ψ S T) (F : GlobalTheory.RealWeil.BB ψ S T), (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F).1 := by
  first | exact @GlobalTheory.Mem.Lift.exists_isCCR_theta | exact GlobalTheory.Mem.Lift.exists_isCCR_theta | (intros; apply GlobalTheory.Mem.Lift.exists_isCCR_theta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.smoothAutomorphicForm_rightTranslate_finiteAdelic : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ k ∈ GfC V, IsAutFunSm θ V (rTr V k φ) := by
  first | exact @GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin | exact GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin | (intros; apply GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.TC.inv_map_mul_map_mul_cancel_complex_embedding {n : ℕ} {E : Type} [Field E] (f : E →+* ℂ) (γ : GL (Fin n) E) (M : Matrix (Fin n) (Fin n) ℂ) :
    ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map f * ((γ : Matrix (Fin n) (Fin n) E).map f * M) = M := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul]
  simp

theorem GlobalTheory.Mem.Col2.TC.tr_eq_of_isTr : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY → ∀ (b : (I.stp u a i).β) (g : (I.stp u a i).G b) (h : (I.chain l u a).Y i → ℂ) (s s' : (I.chain l u a).Y i), IsTr (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) ((I.stp u a i).gam b g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E)) (eY s') (eY s) → (I.stp u a i).tr B.fields.emb B.embLL b g h s = B.embLL (((I.stp u a i).chr b g : B.LLˣ) : B.LL) * h s' := by
  intro B X I _ _ l Z u a i hi eY hId b g h s s' hT
  have key : s' = frMul B.fields.emb B.embLL ((I.stp u a i).gam b g)⁻¹ s := by
    apply Subtype.ext
    funext τ
    have h1 : s.1 τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z))
        (((I.stp u a i).gam b g : GL (Fin (B.R.N i)) B.fields.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E) τ * s'.1 τ := by
      have := hT τ
      rw [hId, hId] at this
      exact this
    have hf : embAt B.embLL B.fields.emb τ = Formalism.L2.Forms.embT (I.rec7 l Z) τ := B.fields_embC τ
    show s'.1 τ = ((((I.stp u a i).gam b g)⁻¹ : GL _ _) : Matrix _ _ _).map (embAt B.embLL B.fields.emb τ) * s.1 τ
    rw [h1, hf]
    exact (GlobalTheory.Mem.Col2.TC.inv_map_mul_map_mul_cancel_complex_embedding _ _ _).symm
  show B.embLL _ * h (frMul B.fields.emb B.embLL ((I.stp u a i).gam b g)⁻¹ s) = _
  rw [← key]
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}

abbrev recOf (Z : Later B C) : D7 := assemble B C Z.W Z.V Z.S Z.N Z.G

variable {Z : Later B C} (Z' : Later B C)



def atTTRe {u : B.Word} (A : AtTTied (D := recOf Z) u) : AtTTied (D := recOf Z') u := { A with }



def clsRe {u : B.Word} {i : ℕ} {hi : i ≤ B.R.m} (K : ClsTied (D := recOf Z) u i hi) : ClsTied (D := recOf Z') u i hi := { K with }



def valRe {u : B.Word} {eV : (C.mem u).A.vT ≃ PlT (recOf Z) u} {i : ℕ} {hi : i ≤ B.R.m} {K : ClsTied (D := recOf Z) u i hi}
    (W : ValTied (D := recOf Z) u eV i hi K) : ValTied (D := recOf Z') u eV i hi (clsRe Z' K) := { W with }



def lvRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {i : ℕ} {hi : i ≤ B.R.m} (P : LvTied (D := recOf Z) u A i hi) :
    LvTied (D := recOf Z') u (atTTRe Z' A) i hi := { P with }



def clsPRe {u : B.Word} (K : ClsPTied (D := recOf Z) u) : ClsPTied (D := recOf Z') u := { K with }



def valPRe {u : B.Word} {K : ClsPTied (D := recOf Z) u} (W : ValPTied (D := recOf Z) u K) :
    ValPTied (D := recOf Z') u (clsPRe Z' K) := { W with }



def tilRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {K : ClsPTied (D := recOf Z) u} {P : LvTied (D := recOf Z) u A B.R.m le_rfl}
    (Tl : TilTied (D := recOf Z) u A K P) : TilTied (D := recOf Z') u (atTTRe Z' A) (clsPRe Z' K) (lvRe Z' P) := { Tl with }



def tilAdRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {K : ClsPTied (D := recOf Z) u} {P : LvTied (D := recOf Z) u A B.R.m le_rfl}
    {Tl : TilTied (D := recOf Z) u A K P} {Km : ClsTied (D := recOf Z) u B.R.m le_rfl} (Ta : TilAd (D := recOf Z) Tl Km) :
    TilAd (D := recOf Z') (tilRe Z' Tl) (clsRe Z' Km) := { Ta with }



def chartRe {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {i : ℕ} {hi : i ≤ B.R.m} {cl : Type}
    {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    (K : LevelChart (recOf Z) T bad i hi stab lat) : LevelChart (recOf Z') T bad i hi stab lat := { K with }



def lvGRe {u : B.Word} {T : ℕ} {res : ∀ v : (C.mem u).A.vT, 𝓞 B.host.E →+* (C.mem u).A.Fv v} {i : ℕ} {hi : i ≤ B.R.m}
    {lat : (C.mem u).C.cls i → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    (L : LevelCompatibleLattices (D := recOf Z) (u := u) (C.fm u) T res i hi lat) : LevelCompatibleLattices (D := recOf Z') (u := u) (C.fm u) T res i hi lat := { L with }



def formsRe {u : B.Word} {Ch : ℕ → Type} {chOf : ∀ i, (C.mem u).C.cls i → Ch i} (T : FormsTiedSym (recOf Z) u Ch chOf) :
    FormsTiedSym (recOf Z') u Ch chOf :=
  { T with
    atT := atTTRe Z' T.atT
    cls := fun i hi h => clsRe Z' (T.cls i hi h)
    val := fun i hi h => valRe Z' (T.val i hi h)
    lv := fun i hi => lvRe Z' (T.lv i hi)
    ch := fun i h1 h2 β => chartRe Z' (T.ch i h1 h2 β)
    valC := fun i h1 h2 => { T.valC i h1 h2 with }
    dilC := fun i h1 h2 => { T.dilC i h1 h2 with }
    lvC := fun i h1 h2 => lvGRe Z' (T.lvC i h1 h2)
    clsP := clsPRe Z' T.clsP
    valP := valPRe Z' T.valP
    til := tilRe Z' T.til
    tilAd := tilAdRe Z' T.tilAd }



def hermChRe (H : Formalism.L2.Herm.HermColsCh (recOf Z)) : Formalism.L2.Herm.HermColsCh (recOf Z') := { H with }



def atTRe {u : B.Word}
    {e : (C.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 B.host.F) // (((C.mem u).A.T : ℕ) : 𝓞 B.host.F) ∈ v.asIdeal}}
    {eF : ∀ v : (C.mem u).A.vT, (C.mem u).A.Fv v ≃+* (𝓞 B.host.F ⧸ (e v).1.asIdeal)} (A : Formalism.L2.Herm.AtT (recOf Z) u e eF) :
    Formalism.L2.Herm.AtT (recOf Z') u e eF := { A with }



def hermRe (H : Formalism.L2.Herm.ColsHermS (recOf Z)) : Formalism.L2.Herm.ColsHermS (recOf Z') :=
  { H with
    base := hermChRe Z' H.base
    atT := fun u => atTRe Z' (H.atT u)
    ad := { H.ad with } }



def colsRe (T : ColsTiedSym (recOf Z)) : ColsTiedSym (recOf Z') :=
  { T with
    herm := hermRe Z' T.herm
    forms := fun u => formsRe Z' (T.forms u)
    gl_const := T.gl_const }

end GlobalTheory.Mem.Top.ColOwe

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def Chart (u : B.Word) (a : I.ι) (i : ℕ) : Type :=
  Set.range fun c : (I.stp u a i).Cl => (c.1, cosetIn ((I.stp u a i).rep c))

def chartOf (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : Chart I u a i :=
  ⟨(c.1, cosetIn ((I.stp u a i).rep c)), c, rfl⟩

structure AdmK (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} (k : Ch → GA B (B.R.N i)) : Prop where
  std : ∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (k β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)
  off : ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v →
    (a = I.mu0 ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (k β) = 1
  T : ∀ β (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
    HasRes P.1 (adAt B.host.F P.1 (((k β)⁻¹ : GA B (B.R.N i)).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)

theorem finite_chart (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) : Finite (Chart I u a i) := by
  have h := (l.ch u a).step i
  haveI : Finite (I.stp u a i).Cl := @Finite.instSigma _ _ inferInstance h.fin_orb
  exact (Set.finite_range _).to_subtype

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem not_underQ_mu0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ v : HeightOneSpectrum (𝓞 B.host.F), ¬ I.UnderQ I.mu0 v := by
  intro B X I _ v ⟨P, hP, _⟩
  have e : P ∈ (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) := I.twistPrimes_reference_tuple_eq_empty ▸ hP
  simp at e

end GlobalTheory.Mem.Col2.TC
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.not_twistPlace_referenceTuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → ∀ v : HeightOneSpectrum (𝓞 B.host.F), ¬ I.UnderQ I.mu0 v := by
  intro B X I _ v ⟨P, hP, _⟩
  have hEmpty : P ∈ (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) :=
    I.twistPrimes_reference_tuple_eq_empty ▸ hP
  simp at hEmpty
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ResF

variable {D : D7} {u : D.what₂.Word}

theorem conj_conj_host (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

theorem exists_intF (z : 𝓞 D.host.E) (hz : D.host.conj (z : D.host.E) = z) :
    ∃ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF = z := by
  have hF : (z : D.host.E) ∈ D.host.F := (D.host.conjE_mem_hostF_iff _).2 hz
  refine ⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩
  · exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp
      (RingOfIntegers.isIntegral_coe z)
  · rfl

theorem res_algebraMap_surjective (A : AtTTied u) (v : (D.mem u).A.vT) :
    Function.Surjective ((A.res v).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) := by
  intro r
  obtain ⟨y, rfl⟩ := A.res_surj v r
  let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := fun y => rfl
  obtain ⟨t, ht⟩ := exists_intF (D := D) (A.piU + cO A.piU) (by
    push_cast; simp only [hcO, map_add (f := _), conj_conj_host]; ring)
  obtain ⟨z, hz⟩ := exists_intF (D := D) (y * cO A.piU + cO y * A.piU) (by
    push_cast; simp only [hcO, map_add (f := _), map_mul, conj_conj_host]; ring)
  have htp : t ∉ (A.eV v).1.asIdeal := by
    rw [A.res_v, ht, map_add (f := _), A.res_pi, zero_add]; exact A.res_conj v _ rfl
  obtain ⟨s, i, hi, hsi⟩ := ((A.eV v).1.isMaximal).exists_inv htp
  have hi0 : A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) i) = 0 := (A.res_v v i).1 hi
  have hst : A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s) * A.res v (cO A.piU) = 1 := by
    have := congrArg (fun x => A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x)) hsi
    simp only [map_add (f := _), map_mul, map_one, hi0, add_zero, ht, A.res_pi, zero_add] at this
    exact this
  refine ⟨s * z, ?_⟩
  simp only [RingHom.comp_apply, map_mul, hz, map_add (f := _), A.res_pi, mul_zero, add_zero]
  rw [mul_comm (A.res v y), ← mul_assoc, hst, one_mul]

theorem exists_fv_equiv (A : AtTTied u) (v : (D.mem u).A.vT) :
    ∃ e : (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (A.eV v).1.asIdeal),
      ∀ a : 𝓞 D.host.F, e (A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a := by
  have hker : (A.eV v).1.asIdeal = RingHom.ker ((A.res v).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) := by
    ext x; rw [RingHom.mem_ker]; exact A.res_v v x
  refine ⟨((Ideal.quotEquivOfEq hker).trans
    (RingHom.quotientKerEquivOfSurjective (res_algebraMap_surjective A v))).symm, fun a => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem fv_equiv_quot : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X),
    ColIn.Ok I → TC.Pins B X →
    ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (u : B.Word)
      {Ch : ℕ → Type} {chOf : ∀ i, ((TC.rec7 I l Z).mem u).C.cls i → Ch i}
      (F : Formalism.L2.Forms.FormsTiedSym (TC.rec7 I l Z) u Ch chOf),
      TC.StdF I l Z u F → ∀ v : ((TC.rec7 I l Z).mem u).A.vT,
      ∃ e : ((TC.rec7 I l Z).mem u).A.Fv v ≃+* (𝓞 (TC.rec7 I l Z).host.F ⧸ (F.atT.eV v).1.asIdeal),
        ∀ a : 𝓞 (TC.rec7 I l Z).host.F,
          e (F.atT.res v (algebraMap (𝓞 (TC.rec7 I l Z).host.F) (𝓞 (TC.rec7 I l Z).host.E) a)) =
            Ideal.Quotient.mk _ a := by
  intro B X I _ _ l Z u Ch chOf F _ v
  exact exists_fv_equiv F.atT v

end GlobalTheory.Mem.Col2.ResF

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

theorem GStep.Ok.reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} (h : S.Ok)
    (pref : ∀ b, S.D b → Prop) : (S.reRep pref).Ok :=
  ⟨h.fin_orb, h.fin_stab, h.unit, h.root, h.lsh_smul, h.lsh_full_lat, h.stab_inj⟩

theorem GStep.Free.reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n} (h : S.Free)
    (pref : ∀ b, S.D b → Prop) : (S.reRep pref).Free := fun b g d hd => h b g d hd

namespace TC

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.xi_unitary (h : I.Ok) (a : I.ι) : (I.xi a).IsUnitary := by
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  exact HChar.isUnitary_of_order hn ((h.xi_reads a).orderDvd hpow)

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.unrepresented_step_conditions (h : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) : (I.stp0 u a i).Ok := by
  have hX : B.fields.Ok := (base_fields_primes_ok B X).1
  have hPr : (B.primes X).Ok := (base_fields_primes_ok B X).2.1
  refine StepOk.stepY_ok _ _ _ _ hX _ _ ?_ ?_ ?_
  · rintro ⟨_ | b, hb⟩ P
    · exact topLev_finiteIndex I.Ch I.sel (I.tup a) (I.cst a) I.Ps i P
    · exact (LevFin.levQ_finiteIndex_and_root I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hX hPr
        (h.idx_ok a) i (hb.1 rfl) b P).1
  · rintro ⟨_ | b, hb⟩ P g
    · obtain ⟨m, hm, hk⟩ := topLev_root I.Ch I.sel (I.tup a) (I.cst a) I.Ps i P
      exact ⟨m, hm, hk g⟩
    · exact (LevFin.levQ_finiteIndex_and_root I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hX hPr
        (h.idx_ok a) i (hb.1 rfl) b P).2 g
  · exact fun N hN => (CosetFin.ysAt_finite_nonempty B.R I.sel (I.tup a) (I.cst a) i N hN).1

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.stp_ok (h : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) : (I.stp u a i).Ok := (h.unrepresented_step_conditions u a i).reRep _

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.stp_zero_free (h : I.Ok) (u : B.Word) (a : I.ι) : (I.stp u a 0).Free :=
  GStep.Free.reRep (stepAt_zero_free I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u (base_fields_primes_ok B X).1
    (base_fields_primes_ok B X).2.1 (base_fields_primes_ok B X).2.2.2.2 (h.idx_ok a).zero_G) _

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.chIn_ok (h : I.Ok) (u : B.Word) (a : I.ι) : (I.chIn u a).Ok := by
  refine
    { step := h.stp_ok u a
      rho_norm := ?_
      rho'_norm := ?_
      DG_pos := DGam_pos (posStar_of_ok (base_fields_primes_ok B X).1) B.R
      dvd_DG := ?_ }
  · intro i _ c
    show ‖((rhoAt I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ)‖ = 1
    exact norm_rhoAt I.SQ I.C (h.xi_unitary a) i _
  · intro i _ c
    show ‖((rhoAt' I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ)‖ = 1
    exact norm_rhoAt' I.SQ I.C (h.xi_unitary a) i _
  · intro i hi c
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have hf := h.stp_zero_free u a
      have : Subsingleton ((I.stp u a 0).Stab c) :=
        ⟨fun x y => Subtype.ext ((hf c.1 x.1 _ x.2).trans (hf c.1 y.1 _ y.2).symm)⟩
      haveI : Nonempty ((I.stp u a 0).Stab c) := ⟨1⟩
      have hcard : Nat.card ((I.stp u a 0).Stab c) = 1 := Nat.card_unique
      rw [show Nat.card (((I.chIn u a).S 0).Stab c) = 1 from hcard]
      exact one_dvd _
    · exact stepY_dvd _ _ _ _ ((I.Tp a).pref u i) (base_fields_primes_ok B X).1 B.R (N_mem_gamRanks B.R hpos hi) c.1 ((I.stp u a i).rep c)

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.idx0 (h : I.Ok) (a : I.ι) : Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) := by
  obtain ⟨b, -⟩ := (h.idx_ok a).zero_uniq
  exact ⟨⟨some b, by simp only [Option.isSome_some, true_iff]; exact lt_of_lt_of_le (by norm_num) B.R.two_le_m⟩⟩

theorem rep_L_lattice (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) :
    Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L :=
  ((I.stp u a i).rep c).1.1.deco.2.L_lattice

theorem ok_chains : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.chIn u a).Ok ∧ Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) ∧ ∀ i c, Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L :=
  fun _ h u a => ⟨h.chIn_ok u a, h.idx0 a, fun i c => rep_L_lattice u a i c⟩

end TC

end GlobalTheory.Mem.Col2

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem cosetIn_mv_up : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (j : ℕ), X.Ok → Pr.Ok → (∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) → ∀ (q : PtAt R sel mu cst u j) (P : Pr.vT u) (x : Sp X.E (R.N j)), x ∈ q.1.1.deco.1.N → q.1.1.deco.1.f P x = 1 → cosetIn (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x) : PtAt R sel mu cst u j) = cosetIn q := by
  intro X Pr R sel S mu cst u j hX hPr hQ q P x hx hf
  have hP := moveHyp_of_ok hPr u P
  have h := mv_up (Pr.T u) q P hP (T_unif hX hPr u P) (fun w => ne_of_T_notMem hPr u P (hQ w.1 w.2))
    (ysAt_off sel mu cst hPr u hQ j P) hx hf
  have hs := (upN_spec q.1.1.deco.2.lat q.1.1.deco.2.uni P.1 hP.ne hx).2.2.1
  have key : ∀ w : Pr.vGs, (q.1.1.deco.1.up P (Pr.T u : 𝓞 X.E) x).at w.1 = q.1.1.deco.1.at w.1 := fun w =>
    (hs w.1 (hP.sg w).1 (hP.sg w).2).localization_eq
  have hfr : frsF sel mu (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1 = frsF sel mu q.1.1 := by
    funext P'
    unfold frsF
    split_ifs with hw
    · show (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1.deco.1.liftFr ⟨P'.1, hw⟩ = q.1.1.deco.1.liftFr ⟨P'.1, hw⟩
      rw [h.1]
      unfold Deco.liftFr
      rw [key ⟨P'.1, hw⟩]
      rfl
    · show (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1.1.2 _ = q.1.1.1.2 _
      rw [h.2.1]
  funext P'
  unfold cosetIn
  rw [hfr, h.2.2]

end GlobalTheory.Mem.Col2

end
end
