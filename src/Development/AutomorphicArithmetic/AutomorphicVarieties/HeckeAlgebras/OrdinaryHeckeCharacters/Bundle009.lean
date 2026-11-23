module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.EqOnTors
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.HeckePolCoeff
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.levelUR2BaseAct :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K : H.Lev) (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R) (J : Ideal R), H.IsJ θ a K D₀ ψ₀ lam J → ∃ μ : R →+* Module.End A (H.MK θ a K), (∀ b y, μ (lam b) y = b • y) ∧ RingHom.ker μ = J ∧ (H.MK θ a K = ⊥ ∨ ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K), H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))) := by
  intro L Ω _ _ _ _ _ l _ n c H _ A _ _ _ θ _ a K R _ _ D₀ ψ₀ lam J hJ
  rcases hJ with ⟨h0, hJ⟩ | ⟨x, x1, f, hne, hmap, hsurj, hlam, hker⟩
  · haveI : Subsingleton (H.MK θ a K) := by
      rw [h0]
      infer_instance
    haveI : Subsingleton (Module.End A (H.MK θ a K)) := inferInstance
    let μ : R →+* Module.End A (H.MK θ a K) :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    refine ⟨μ, ?_, ?_, Or.inl h0⟩
    · intro b y
      exact Subsingleton.elim _ _
    · rw [hJ]
      ext t
      simp only [RingHom.mem_ker, Submodule.mem_top, iff_true]
      exact Subsingleton.elim _ _
  · refine ⟨(UpperTheory.V.Hi.heckeAlg (H.MK θ a K) (H.op A)).val.toRingHom.comp f.toRingHom, ?_, ?_, Or.inr ⟨x, x1, f, hmap, fun t => rfl⟩⟩
    · intro b y
      have h := hlam b
      show ((f (lam b) : Module.End A (H.MK θ a K))) y = b • y
      rw [h]
      rfl
    · rw [hker]
      ext t
      simp only [RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      constructor
      · intro ht
        exact Subtype.ext ht
      · intro ht
        rw [ht]
        rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem UpperTheory.V.Hi.partUR2Mem_span {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ}
    {V : s.Lev} (ι : Qbar l ≃+* ℂ) (m : ℕ)
    {lam : Wt L l n} {d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (σ : Submodule ℂ (UA L n → ℂ))
    (F : Fin m → (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ))
    (h : F ∈ Submodule.span ℂ {F : Fin m → (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) | ∀ i ℓ, toForm ι e (F i) ℓ ∈ σ}) :
    ∀ i ℓ, toForm ι e (F i) ℓ ∈ σ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    intro i ℓ
    have : toForm ι e ((0 : Fin m → (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ)) i) ℓ = 0 := by
      funext g
      simp only [toForm, Pi.zero_apply, map_zero]
    rw [this]; exact σ.zero_mem
  | add x y _ _ hx hy =>
    intro i ℓ
    have : toForm ι e ((x + y) i) ℓ = toForm ι e (x i) ℓ + toForm ι e (y i) ℓ := by
      funext g
      simp only [toForm, Pi.add_apply, map_add (f := _)]
    rw [this]; exact σ.add_mem (hx i ℓ) (hy i ℓ)
  | smul a x _ hx =>
    intro i ℓ
    have : toForm ι e ((a • x) i) ℓ = a • toForm ι e (x i) ℓ := by
      funext g
      simp only [toForm, Pi.smul_apply, map_smul]
    rw [this]; exact σ.smul_mem a (hx i ℓ)

theorem UpperTheory.V.Hi.partUR2Mem :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (σ : Submodule ℂ (UA L n → ℂ)) (F : Fin m → (hset Q τ₀).X.Fn ℂ d),
    F ∈ YOf Q ι τ₀ e ξ σ ↔ F ∈ (hset Q τ₀).Big ι ξ ∧ ∀ i ℓ, toForm ι e (F i) ℓ ∈ σ := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V Q c ι m τ₀ lam d e ξ σ F
  constructor
  · intro h
    exact ⟨h.1, UpperTheory.V.Hi.partUR2Mem_span ι m e σ F h.2⟩
  · intro h
    exact ⟨h.1, Submodule.subset_span h.2⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_eq {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    CaseU.cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem cmp_mem {w : Plc L} (x : UA L n) (P : Subgroup (GLw n w)) (hx : cLoc w x ∈ P) :
    CaseU.cmp n w ((away l L n).rangeRestrict x) ∈ P := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · rw [cmp_eq h]
    exact hx
  · unfold CaseU.cmp
    rw [dite_eq_right h]
    exact P.one_mem

private theorem st_away (s : HidaSetting l L Ω) (u : s.St) : ((l : ℕ) : 𝓞 L) ∉ (s.w u).asIdeal := fun h => by
  refine s.St_l u.1 u.2 ((s.hA u.1 _).1 ?_)
  have h1 := (s.hw u.1 _).2 h
  simpa using h1

private theorem UpperTheory.V.Hi.inf_one {s : HidaSetting l L Ω} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n} (hk : k ∈ finU (E := L) (n := n)) :
    infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

private theorem key {s : HidaSetting l L Ω} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {d m : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (F : Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) {x : UA L n} (hx : x ∈ finU (E := L) (n := n))
    (hl : ∀ v : V.frame.Vl, cLoc (s.w v.1) x = 1) (a : Fin m → ℂ) (i : Fin m)
    (h : ∀ g k, ∑ j, a j * F j (g * ((away l L n).rangeRestrict x, 1)) k = F i g k) (ℓ) :
    ∑ j : Fin m, a j • RU L n x (toForm ι e (F j) ℓ) = toForm ι e (F i) ℓ := by
  funext g
  rw [Finset.sum_apply]
  have e1 : ∀ j, RU L n x (toForm ι e (F j) ℓ) g = ℓ (infRep ι lam g⁻¹ (e (F j
      (((away l L n).rangeRestrict g, fun v : V.frame.Vl => cLoc (s.w v.1) g) * ((away l L n).rangeRestrict x, 1))))) := fun j => by
    change toForm ι e (F j) ℓ (g * x) = _
    unfold toForm
    rw [mul_inv_rev, map_mul, UpperTheory.V.Hi.inf_one V ι lam (inv_mem hx), one_mul]
    simp only [map_mul, hl, mul_one, Prod.mk_mul_mk]
  have e2 : ∀ g, F i g = ∑ j, a j • F j (g * ((away l L n).rangeRestrict x, 1)) := fun g => funext fun k => by
    rw [← h g k, Finset.sum_apply]
    rfl
  simp only [Pi.smul_apply, e1]
  unfold toForm
  rw [e2]

  simp only [map_sum, map_smul]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Hi.partUR2Fix :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ (F : Fin m → (hset Q τ₀).X.Fn ℂ d), F ∈ (hset Q τ₀).Big ι ξ → ∀ x ∈ finU (E := L) (n := n), (∀ v : V.frame.Vl, cLoc (s.w v.1) x = 1) → ∀ k : KT n (wt s), (∀ u : s.St, k.1 u = cLoc (s.w u) x) → cLoc (s.w s.v0) x ∈ Kc _ n 1 →
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cLoc w x ∈ KO (w.adicCompletion L) (Fin n)) → (∀ q, cLoc (Q.wq q) x = 1) →
    ∀ (i : Fin m) ℓ, ∑ j : Fin m, ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) k i j • RU L n x (toForm ι e (F j) ℓ) = toForm ι e (F i) ℓ := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V Q c ι m τ₀ lam d e ξ _ F hF x hx hl k hk h0 hS hQ i ℓ
  let u : Ub n s := ⟨(away l L n).rangeRestrict x, Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u =>
    cmp_mem x _ (hk u ▸ k.2 u trivial), cmp_mem x _ h0⟩⟩
  have hu : u ∈ UQ n Q := Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw =>
    cmp_mem x _ (hS w hw), Subgroup.mem_iInf.2 fun q =>
      Subgroup.mem_bot.1 (cmp_mem (l := l) x ⊥ (Subgroup.mem_bot.2 (hQ q)))⟩
  have hk' : toKT n s u = k := Subtype.ext (funext fun a => (cmp_eq (st_away s a) x).trans (hk a).symm)
  have h1 := hF.2 u hu
  rw [← hk']
  exact key V ι lam e F hx hl _ i (fun g b => congrFun (congrFun (congrFun h1 i) g) b) ℓ
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem infRep_fin {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n}
    (hk : k ∈ finU (E := L) (n := n)) : infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

private theorem comps {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) [DecidableEq V.frame.Vl] (v : V.frame.Vl) (x y : UA L n)
    (hy : y ∈ locU n (s.w v.1)) :
    (((away l L n).rangeRestrict (x * y), fun u : V.frame.Vl => cLoc (s.w u.1) (x * y)) :
        Ga l L n × GV n (fun u : V.frame.Vl => s.w u.1)) =
      ((away l L n).rangeRestrict x, fun u : V.frame.Vl => cLoc (s.w u.1) x) *
        (1, MonoidHom.mulSingle (fun u : V.frame.Vl => GLw n (s.w u.1)) v (cLoc (s.w v.1) y)) := by
  refine Prod.ext ?_ (funext fun u => ?_)
  · have h : (away l L n).rangeRestrict y = 1 := by
      refine Subtype.ext (funext fun u => GlobalTheory.DefU.LocRet.mem_locU_ne hy fun h => u.2 ?_)
      have h2 : ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.1.under (𝓞 (Lp L))).asIdeal := by
        rw [h, w_under]
        exact v.2
      have h3 : algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ u.1.asIdeal := h2
      rwa [map_natCast] at h3
    rw [map_mul, h]
    rfl
  · change cLoc (s.w u.1) (x * y) = cLoc (s.w u.1) x *
      Pi.mulSingle (M := fun u : V.frame.Vl => GLw n (s.w u.1)) v (cLoc (s.w v.1) y) u
    rw [map_mul]
    congr 1
    by_cases huv : u = v
    · subst huv
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne huv]
      exact GlobalTheory.DefU.LocRet.mem_locU_ne hy fun h =>
        huv (Subtype.ext ((w_under s u.1).symm.trans (h.trans (w_under s v.1))))

theorem UpperTheory.V.Hi.partUR2AtV :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ (v : V.frame.Vl) (j : GLw n (s.w v.1) →* UA L n), (∀ g, j g ∈ locU n (s.w v.1)) → (∀ g, cLoc (s.w v.1) (j g) = g) →
    ∀ (F : Fin m → (hset Q τ₀).X.Fn ℂ d) (g : GLw n (s.w v.1)) (i : Fin m) ℓ, toForm ι e ((hset Q τ₀).atV d v g F i) ℓ = RU L n (j g) (toForm ι e (F i) ℓ) := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V Q c ι m τ₀ lam d e ξ _ v j hj hj' F g i ℓ
  funext x
  have h1 := @comps l _ L Ω _ _ _ _ _ _ s n V (fun a b => Classical.propDecidable (a = b)) v x (j g) (hj g)
  rw [hj'] at h1
  have h2 : infRep (V := V) ι lam (x * j g)⁻¹ = infRep (V := V) ι lam x⁻¹ := by
    rw [mul_inv_rev, map_mul, infRep_fin V ι lam ((finU (E := L) (n := n)).inv_mem (Subgroup.mem_inf.1 (hj g)).1), one_mul]
  change _ = toForm ι e (F i) ℓ (x * j g)
  unfold toForm
  rw [h1, h2]
  rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.heckeDeterminant_satisfies_deformation_relations :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (T : Type) [CommRing T] [Algebra c.O T] (D : W.GDet n T V.frame.G₀) (ψ : ∀ v : V.frame.Vl, Fin n → V.frame.Gv v →* Tˣ) (Gd : (T →ₐ[c.O] Qbar l) → Prop),
    (∀ t : T, (∀ x, Gd x → x t = 0) → t = 0) →
    (∀ x, Gd x → ∃ ρ : V.frame.G₀ →* GL (Fin n) (Qbar l), PU r ι lam ρ ∧ D.map x.toRingHom = W.GDet.ofRep (W.mat ρ) ∧ ∀ v, W.HasFlag (ρ.comp (V.frame.φ v)) fun i => W.pushCh x.toRingHom (ψ v i)) →
    (∀ i g, D.lam i (V.frame.star c.O T n (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1)) ∧
    (∀ v (g : Fin n → V.frame.Gv v) (h : V.frame.G₀), D.tr (MonoidAlgebra.single h 1 * V.frame.oEl v (ψ v) g) = 0) ∧
    ∀ u, ∀ g ∈ r.Ip u, ∀ h : V.frame.G₀, D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) = 0 := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V c r ι lam T _ _ D ψ Gd hsep hex
  choose ρ hPU hD hfl using hex
  obtain ⟨hP, hO, hI⟩ := JEx.rels V.frame c.O T D ψ (X := {x // Gd x}) (Qbar l) (fun x => x.1) (fun x => ρ x.1 x.2)
    (fun a ha => hsep a fun x hx => ha ⟨x, hx⟩) (fun x => hD x.1 x.2) (fun x => (hPU x.1 x.2).form) (fun x => hfl x.1 x.2)
  refine ⟨(AlgebraTools.Det.polarIffLam _ _ _ _ D).1 hP, fun v g h => AlgebraTools.Det.killsLam D _ (hO v g) _ 1 le_rfl hn,
    fun u g hg h => AlgebraTools.Det.killsLam D _ (hI g fun x => ?_) _ 1 le_rfl hn⟩
  obtain ⟨t, ht, ht1⟩ := JEx.teich c r
  obtain ⟨a, ha⟩ := (hPU x.1 x.2).type t ht u
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  have h1 : a * ρ x.1 x.2 g * a⁻¹ = 1 := by
    refine Units.ext ((ha g hg1).trans ?_)
    have e : ∀ i, t i g = 1 := fun i => ht1 i g (Subgroup.mem_iInf.1 hg2 i)
    simp only [e, Units.val_one, map_one, Matrix.diagonal_one]
  exact conj_eq_one_iff.1 h1
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.exists_ordinaryCharacters_heckeAlgebra :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : HD Q ι Λ), (hset Q R.τ₀).Ax →
    ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (φ : Λ.Λ →ₐ[c.O] T) (gen : (hset Q R.τ₀).Op → T), (∀ i, gen i - algebraMap c.O T (R.a i) ∈ maximalIdeal T) →
    ∀ ψ : ∀ v : V.frame.Vl, Fin n → Dec (F := L) (s.A v.1) →* Tˣ, (∀ v i, Alg.AdicCont (maximalIdeal T) fun g => (ψ v i g : T)) →
    (∀ (v : V.frame.Vl) (i : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)) (y : Uo ((s.w v.1).adicCompletion L)), (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = y →
      (ψ v i g * (hset Q R.τ₀).epsV T v g ^ (i : ℕ) : Tˣ) * φ (R.θ (eV n (hset Q R.τ₀).Sl v i y)) = 1) →
    (∀ (v : V.frame.Vl) (j : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)), (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = unif _ →
      ((∏ i with i ≤ j, ψ v i g * (hset Q R.τ₀).epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
    ∀ v i, r.IsPsi v i (ψ v i) ∧ W.pushCh (φ : Λ.Λ →+* T) (Λ.κ v i) = (ψ v i).comp (V.frame.Iv v).subtype := by
  intro l _ L Ω _ _ _ _ _ _ s n V Q c r ι Λ R hAx T _ _ _ φ gen hgen ψ hc hu hϖ v
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : Finite (ResidueField T) := Finite.of_surjective _ (Alg.resMap_bijective c.O T).2
  have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := hAx.art_spec v
  have hI : ∀ i (g : Dec (F := L) (s.A v.1)) (hg : g ∈ V.frame.Iv v), (ψ v i g : T) = φ (Λ.κ v i ⟨g, hg⟩) := by
    intro i g hg
    have h1 := hu v i (ineIncl (s.hw v.1) ⟨g, hg⟩) g ⟨_, JEx.art_ine _ ha ⟨g, hg⟩⟩ rfl rfl
    have h2 := congrArg (fun z : Λ.Λˣ => φ z) (R.theta v i (ineIncl (s.hw v.1) ⟨g, hg⟩) g hg ⟨_, JEx.art_ine _ ha ⟨g, hg⟩⟩ rfl rfl)
    have h3 : φ ((hset Q R.τ₀).epsV Λ.Λ v g) = (hset Q R.τ₀).epsV T v g := φ.commutes _
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_one, map_one, h3, mul_assoc] at h1 h2
    exact (left_inv_eq_right_inv h1 ((mul_comm _ _).trans h2))
  choose ψ₀ hψ₀ hκ using Λ.inert v
  have hI' : ∀ i (g : Dec (F := L) (s.A v.1)), (g : G L Ω) ∈ Ine (F := L) (s.A v.1) → (ψ v i g : T) = φ (ψ₀ i g) := by
    intro i g hg
    rw [hI i g hg, hκ]
    rfl
  obtain ⟨x, hx⟩ := ha.surj (unif _)
  let p : T →+* ResidueField c.O := Alg.res c.O T
  have hx' : ∀ i, W.pushCh p (ψ v i) (Subgroup.inclusion (Weil_le_Dec _) x) = r.psib v i (Subgroup.inclusion (Weil_le_Dec _) x) := by
    intro i
    refine mul_right_cancel (JEx.eq_of_prod
      (fun i : Fin n => W.pushCh p (ψ v i) (Subgroup.inclusion (Weil_le_Dec _) x) *
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) ^ (i : ℕ))
      (fun i : Fin n => r.psib v i (Subgroup.inclusion (Weil_le_Dec _) x) *
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) ^ (i : ℕ)) (fun j => Units.ext ?_) i)
    have h1 := congrArg p (hϖ v j x (Subgroup.inclusion (Weil_le_Dec _) x) rfl hx)
    have h2 := R.res.unif v j x (Subgroup.inclusion (Weil_le_Dec _) x) rfl hx
    have h3 := (Alg.res_eq_zero_iff c.O T _).2 (hgen (.inr (v, j)))
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h3
    have h4 : p ((hset Q R.τ₀).epsV T v (Subgroup.inclusion (Weil_le_Dec _) x)) =
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) := (Alg.res c.O T).commutes _
    refine Eq.trans ?_ ((h1.trans h3).trans h2.symm)
    simp only [Units.coe_prod, map_prod, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    exact Finset.prod_congr rfl fun k _ => congrArg₂ (· * ·) rfl (congrArg (· ^ (k : ℕ)) h4.symm)
  intro i
  refine ⟨⟨hc v i, fun g => ?_, fun g => ?_⟩, MonoidHom.ext fun g => Units.ext (hI i g.1 g.2).symm⟩
  · have h1 : IsLocallyConstant (W.pushCh p (ψ v i)) :=
      IsLocallyConstant.desc _ Units.val (JEx.res_lc (O := c.O) (hc v i)) Units.val_injective
    let β : Dec (F := L) (s.A v.1) →* (ResidueField c.O)ˣ := r.psib v i
    have h2 : IsLocallyConstant β := JEx.lc_of_open _ (r.psib_open v i)
    have h3 := JEx.char_triv (s.hw v.1) ha (W.pushCh p (ψ v i) / β) (h1.div h2) (fun y hy => by
      rw [MonoidHom.div_apply, div_eq_one]
      refine Units.ext ?_
      exact (congrArg p (hI' i y hy)).trans ((Alg.res_map φ _).trans ((hψ₀ i).red y))) x hx (by rw [MonoidHom.div_apply, div_eq_one]; exact hx' i)
    have h4 : W.pushCh p (ψ v i) g / β g = 1 := DFunLike.congr_fun h3 g
    exact congrArg Units.val (div_eq_one.1 h4)
  · obtain ⟨k, hk⟩ := g.2
    have h1 := JEx.eq_on_tors (s.hw v.1) (ψ v i) (W.pushCh (φ : Λ.Λ →+* T) (ψ₀ i)) (hc v i) (JEx.cont_map φ (hψ₀ i).cont)
      (fun y hy => Units.ext (hI' i y hy)) g.1 (l ^ k) (pow_pos (Fact.out : l.Prime).pos k)
      ((QuotientGroup.eq_one_iff _).1 ((map_pow (QuotientGroup.mk' _) _ _).trans hk))
    exact (congrArg Units.val h1).trans ((congrArg φ ((hψ₀ i).mu g)).trans (φ.commutes _))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.heckeDeterminant_reduction_eq_residual :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : HD Q ι Λ), (hset Q R.τ₀).Ax →
    ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (gen : (hset Q R.τ₀).Op → T), (∀ i, gen i - algebraMap c.O T (R.a i) ∈ maximalIdeal T) →
    ∀ D : W.GDet n T V.frame.G₀, D.IsCont (maximalIdeal T) →
    (∀ (w : (hset Q R.τ₀).Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
      D.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
    D.map (Alg.res c.O T : T →+* ResidueField c.O) = r.Dbar := by
  intro l _ L Ω _ _ _ _ _ _ s n V Q c r ι Λ R hA T _ _ _ gen hgen D hD hF
  refine JEx.red_eq r D hD _ hA.dense ?_
  rintro g ⟨w, hw, B, σ, hB, hσ, rfl⟩
  have h1 := hF ⟨w, hw⟩ B σ hB hσ
  have h2 := R.res.frob ⟨w, hw⟩ B σ hB hσ
  refine (congrArg (Polynomial.map _) h1).trans (Eq.trans ?_ h2.symm)
  rw [JEx.heckePol_map]
  congr 1
  funext j
  split_ifs with h
  · have h3 := (Alg.res_eq_zero_iff c.O T _).2 (hgen (.inl (⟨w, hw⟩, ⟨j - 1, h.2⟩)))
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h3
    exact h3
  · exact map_one _
end
