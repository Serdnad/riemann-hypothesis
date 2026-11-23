module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TupOfOneMemLabT
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem formsExport_eq : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (hE : IsEmpty D.nd.Loc)
    (hfg : ∀ i j b, (BsupT D T S i j b).FG) (hst : HkStab D T S In) (sd : SigData D T) (rho : RhoFam D T)
    (hrho : ∀ i σ b, Continuous fun g =>
      ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) (he : EIdem D)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T)
    (i : (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
    ∃ e : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b ≃ₗ[FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)]
        Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b,
      (∀ x, x ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ↔
        e x ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b) ∧
      (∀ g x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).actG i j b g x) =
        actG ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
          (In.rho j h1 h2) (In.chi j h1 h2) g (e x)) ∧
      ∀ k P x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).hkF i j b k P x) =
        algebraMap ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)
            (FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)) (cHkT D T i b P : T.O i) ^ k •
          GlobalTheory.HeightCounting.hkF D ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
            (In.hL j) (In.hs j h1 h2) k P (e x) := by
  intro D S In T hE hfg hst sd rho hrho he Pq wt i j b h1 h2
  let i' : T.Tw := i
  have hW : WKr D S j = (S.A j).WK := WKr_of D S h1 h2
  let e : (KT D T i' b ⊗[S.Ks] ↥(WKr D S j)) ≃ₗ[KT D T i' b] (KT D T i' b ⊗[S.Ks] ↥(S.A j).WK) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (KT D T i' b) (KT D T i' b)) (LinearEquiv.ofEq _ _ hW)
  have he1 : ∀ (a : KT D T i' b) (w : ↥(WKr D S j)), e (a ⊗ₜ[S.Ks] w) = a ⊗ₜ[S.Ks] (LinearEquiv.ofEq _ _ hW w) :=
    fun a w => rfl
  have hbc : ∀ (f : Module.End S.Ks ↥(WKr D S j)) (f' : Module.End S.Ks ↥(S.A j).WK),
      (∀ w, ((f w : ↥(WKr D S j)) : S.WL j) = (f' (LinearEquiv.ofEq _ _ hW w) : S.WL j)) →
      ∀ y, e (Module.End.baseChangeHom S.Ks (KT D T i' b) _ f y) = Module.End.baseChangeHom S.Ks (KT D T i' b) _ f' (e y) := by
    intro f f' hf y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a w =>
      show a ⊗ₜ[S.Ks] (LinearEquiv.ofEq _ _ hW (f w)) = a ⊗ₜ[S.Ks] (f' (LinearEquiv.ofEq _ _ hW w))
      exact congrArg (a ⊗ₜ[S.Ks] ·) (Subtype.ext (hf w))
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, map_add (f := _), map_add (f := _)]
  have hc : ∀ g', cR D S In.chi j g' = chiL S j (In.chi j h1 h2) g' := fun g' => dif_pos ⟨h1, h2⟩
  have hsm : ∀ (r : T.O i') (y : KT D T i' b ⊗[S.Ks] ↥(WKr D S j)),
      e ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • y) =
        (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • e y := fun r y => e.map_smul _ y
  have hsm' : ∀ (r : T.O i') (y : KT D T i' b ⊗[S.Ks] ↥(S.A j).WK),
      e.symm ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • y) =
        (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • e.symm y := fun r y => e.symm.map_smul _ y
  refine ⟨e, ?_, ?_, ?_⟩
  · let eO : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b →ₗ[(T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i] Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b :=
      { toFun := fun y => e y, map_add' := fun y z => e.map_add y z, map_smul' := fun r y => hsm r y }
    let eO' : Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b →ₗ[(T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i] (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b :=
      { toFun := fun y => e.symm y, map_add' := fun y z => e.symm.map_add y z, map_smul' := fun r y => hsm' r y }
    have hle1 : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ≤ (Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b).comap eO := by
      show BsupT D T S i' j b ≤ _
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, rfl⟩
      exact (Submodule.subset_span ⟨LinearEquiv.ofEq _ _ hW w, hw, rfl⟩ : _ ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b)
    have hle2 : Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b ≤ ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b).comap eO' := by
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, rfl⟩
      exact (Submodule.subset_span ⟨(LinearEquiv.ofEq _ _ hW).symm w, hw, rfl⟩ : _ ∈ BsupT D T S i' j b)
    intro x
    refine ⟨fun hx => hle1 hx, fun hx => ?_⟩
    have h := hle2 hx
    rw [Submodule.mem_comap] at h
    change e.symm (e x) ∈ _ at h
    exact Eq.mp (congrArg (fun (z : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b) => z ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b) (e.symm_apply_apply x)) h
  · intro g x
    change e ((actEndT D T S In.rho In.chi i' j b (S.eG.symm g)) x) =
      (actEnd ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b (In.rho j h1 h2) (In.chi j h1 h2) (S.eG.symm g)) (e x)
    change e ((readK D T i' b (cR D S In.chi j (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(WKr D S j) (rhoR D S In.rho j (S.eG.symm g)) x) =
      (readK D T i' b (chiL S j (In.chi j h1 h2) (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(S.A j).WK (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (e x)
    rw [LinearEquiv.map_smul, hbc _ (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (fun w => rfl) x, hc]
  · intro k P x
    change e ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) (cHkT D T i' b P : T.O i')) ^ k •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(WKr D S j) (hLr D S In j k P) x) =
      (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) (cHkT D T i' b P : T.O i')) ^ k •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(S.A j).WK
          (((In.hL j k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK)
            fun x hx => In.hs j h1 h2 k P x hx) (e x)
    rw [LinearEquiv.map_smul, hbc _ _ ?_ x]
    intro w
    rw [hLr, dif_pos ⟨h1, h2⟩]
    rfl

end GlobalTheory.HeightCounting.FormsStep
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

section CapelliMinorMembership

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

def piCoef (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u : Formalism.IndefR.NX.U D.nd) : ↥D.LL0 :=
  (Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ * (((psiUOf D.nd (NX.xiRed D) θ u)⁻¹ : (↥D.LL0)ˣ) : ↥D.LL0)

def eLop (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g

def piLop (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ᶠ u : Formalism.IndefR.NX.U D.nd, ((piCoef D θ u : ↥D.LL0) : D.what₂.LL) • actL D S j (u : G0g D.nd)


open Classical in
def evRoots (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Finset ↥D.LL0 :=
  (Finset.univ.filter fun σ : D.what₂.FT => D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ).image fun σ => In.eig j σ k P

def evPol (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Polynomial ↥D.LL0 :=
  ∏ r ∈ evRoots D S In j k P, (X - C r)

def phiLop (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Module.End D.what₂.LL (S.WL j) :=
  aeval (In.hL j k P) ((evPol D S In j k P).map (algebraMap ↥D.LL0 D.what₂.LL))

def hLT (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  (Module.End.baseChangeHom S.Ks (KT D T i b) ↥(WKr D S j) (hLr D S In j k P) :
    Module.End (KT D T i b) (KT D T i b ⊗[S.Ks] ↥(WKr D S j)))

def piKop (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  ∑ᶠ u : Formalism.IndefR.NX.U D.nd, readT D T i b (piCoef D In.θ u) • (actGT D T S In.rho In.chi i j b (u : G0g D.nd)).toLinearMap

def phiKop (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  aeval (hLT D T S In i j b k P) ((evPol D S In j k P).map (readT D T i b))

theorem hkT_eq (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    hkT D T S In i j b k P = (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i)) ^ k • hLT D T S In i j b k P :=
  rfl

end CapelliMinorMembership

end GlobalTheory.HeightCounting.FormsStep
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem eigenvalue_integral_of_baseChange {O M : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (f : Module.End O M)
    (x : FractionRing O ⊗[O] M) (hx : x ≠ 0) (c : FractionRing O)
    (h : f.baseChange (FractionRing O) x = c • x) : ∃ a : O, algebraMap O (FractionRing O) a = c := by
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hev : (Module.End.baseChangeHom O (FractionRing O) M f).HasEigenvector c x :=
    ⟨Module.End.mem_eigenspace_iff.mpr h, hx⟩
  have key := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap O (FractionRing O))) hev
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, hpf, map_zero,
    Polynomial.eval_map_algebraMap] at key
  have h0 : Polynomial.aeval c p = 0 := by
    by_contra hne
    exact hx ((smul_eq_zero.mp key.symm).resolve_left hne)
  exact IsIntegrallyClosed.isIntegral_iff.mp ⟨p, hp, by rwa [← Polynomial.aeval_def]⟩

section SigMake

variable (D : D7) (T : TwR D.LL0 D.nd) {S : RatDat D.ntw} (In : RatIn D S)

def sigVal (i : T.Tw) (k : ℕ) (P : PlE D.host) : Prop :=
  1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i

def sigLam (i : T.Tw) (j : ℕ) (b : Bool) (σ : D.what₂.FT) (k : ℕ) (P : PlE D.host) : FractionRing (T.O i) :=
  algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)

def SigIdx (i : T.Tw) : Type :=
  {x : Fin (D.R.m + 1) × Bool × D.what₂.FT // 1 ≤ (x.1 : ℕ) ∧ D.what₂.isot (x.1 : ℕ) x.2.2 ≠ ⊥ ∧ D.nd.goodRow x.2.2 ∧
    ∀ k P, sigVal D T i k P → ∃ a : T.O i, algebraMap (T.O i) (FractionRing (T.O i)) a = sigLam D T In i x.1 x.2.1 x.2.2 k P}

instance finSigIdx (i : T.Tw) : Finite (SigIdx D T In i) := Subtype.finite


open Classical in
def sigEig (i : T.Tw) (x : SigIdx D T In i) (k : ℕ) (P : PlE D.host) : T.O i :=
  if h : sigVal D T i k P then (x.2.2.2.2 k P h).choose else 1

theorem sigEig_on (i : T.Tw) (x : SigIdx D T In i) (k : ℕ) (P : PlE D.host) (h : sigVal D T i k P) :
    algebraMap (T.O i) (FractionRing (T.O i)) (sigEig D T In i x k P) = sigLam D T In i x.1.1 x.1.2.1 x.1.2.2 k P := by
  unfold sigEig
  rw [dite_eq_left h]
  exact (x.2.2.2.2 k P h).choose_spec

theorem sigEig_off (i : T.Tw) (x : SigIdx D T In i) (k : ℕ) (P : PlE D.host) (h : ¬ sigVal D T i k P) :
    sigEig D T In i x k P = 1 := by
  unfold sigEig
  rw [dite_eq_right h]

def sigSys (i : T.Tw) (x : SigIdx D T In i) : ℕ × Bool × (ℕ → PlE D.host → T.O i) :=
  ((x.1.1 : ℕ), x.1.2.1, sigEig D T In i x)

def sigDataOf : SigData D T where
  Sig i := ↥(Set.range (sigSys D T In i))
  fin i := @Fintype.ofFinite _ (Set.finite_range (sigSys D T In i)).to_subtype
  jS i s := s.1.1
  jS_range i s := by
    obtain ⟨x, hx⟩ := s.2
    rw [← hx]
    exact ⟨x.2.1, Nat.lt_succ_iff.mp x.1.1.2⟩
  side i s := s.1.2.1
  hEig i s := s.1.2.2
  rowS i s := s.2.choose.1.2.2

end SigMake

theorem sigDataOf_spec (D : D7) (T : TwR D.LL0 D.nd) {S : RatDat D.ntw} (In : RatIn D S) (i : T.Tw)
    (s : (sigDataOf D T In).Sig i) :
    sigSys D T In i s.2.choose = s.1 := s.2.choose_spec

theorem hkB_coe_of_val (D : D7) (T : TwR D.LL0 D.nd) {S : RatDat D.ntw} (In : RatIn D S) (hst : HkStab D T S In)
    (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hv : sigVal D T i k P)
    (x : ↥(BI D T S In i j b)) :
    ((hkB D T S In hst i j b k P x : ↥(BI D T S In i j b)) : FmT D T S i j b) = hkT D T S In i j b k P x := by
  unfold hkB
  rw [dite_eq_left ⟨h1, h2, hv⟩]
  rfl

end GlobalTheory.HeightCounting.FormsStep
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem cHkT_eq_of_isFrob : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) (P : PlE D.host), P ∉ T.S0 i →
    ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    cHkT D T i b P = Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom
      (if b then T.delta i σ else (T.delta i σ)⁻¹) := by
  intro D T i b P hP σ hσ
  have hA := D.nd.plOm.2 P
  have key : ∀ τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) τ →
      T.delta i τ = T.delta i σ := by
    intro τ hτ
    have hmem := inv_mul_mem_Ine_of_isFrob hσ hτ
    have h1 : T.delta i (σ⁻¹ * τ) = 1 := by
      by_contra hne
      exact hP (T.primes_subset_exceptional i ((T.delta_ram i P _ hA).1 ⟨_, hmem, hne⟩))
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  unfold cHkT
  rw [dite_eq_left ⟨σ, hσ⟩, key _ (Exists.choose_spec (⟨σ, hσ⟩ : ∃ τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om,
    IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) τ))]

end GlobalTheory.HeightCounting.FormsStep
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

theorem readT_integral (i : T.Tw) (b : Bool) (x : ↥D.LL0) (hx : IsIntegral ℤ x) :
    ∃ o : T.O i, algebraMap (T.O i) (FractionRing (T.O i)) o = readT D T i b x := by
  have key : ∀ e : ↥D.LL0 →+* FractionRing (T.O0 i),
      ∃ y : T.O0 i, algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = e x := by
    intro e
    have h1 : IsIntegral ℤ (e x) := by
      obtain ⟨p, hp, hpx⟩ := hx
      refine ⟨p, hp, ?_⟩
      have h3 := congrArg e hpx
      rw [map_zero, Polynomial.hom_eval₂] at h3
      rwa [RingHom.ext_int (e.comp (algebraMap ℤ _)) (algebraMap ℤ _)] at h3
    have h2 : IsIntegral (T.O0 i) (e x) := h1.tower_top
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  obtain ⟨y, hy⟩ := key (if b then T.emb0 i else T.emb0b i)
  refine ⟨algebraMap (T.O0 i) (T.O i) y, ?_⟩
  unfold readT
  rw [RingHom.comp_apply, ← hy]
  exact (IsLocalization.map_eq _ _).symm

theorem ksInt_mem (i : T.Tw) (b : Bool) (a : 𝓞 S.Ks) :
    ∃ o : T.O i, algebraMap (T.O i) (FractionRing (T.O i)) o = algebraMap S.Ks (KT D T i b) (a : S.Ks) :=
  readT_integral D T i b _ ((RingOfIntegers.isIntegral_coe a).map S.kKs.toIntAlgHom)

theorem one_tmul_smul (i : T.Tw) (j : ℕ) (b : Bool) (c : S.Ks) (m : ↥(WKr D S j)) :
    ((1 : KT D T i b) ⊗ₜ[S.Ks] (c • m) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) =
      algebraMap S.Ks (KT D T i b) c • ((1 : KT D T i b) ⊗ₜ[S.Ks] m) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]

theorem fmT_eq_zero (i : T.Tw) (j : ℕ) (b : Bool) (h : ¬ (1 ≤ j ∧ j ≤ D.R.m)) (z : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul k m =>
    have hm : m = 0 := by
      exact Subtype.ext (Submodule.mem_bot _ |>.mp ((WKr_off D S h).le m.2))
    rw [hm, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem bsupT_fg_span (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) :
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤ := by
  by_cases h : 1 ≤ j ∧ j ≤ D.R.m
  swap
  · have hz := fmT_eq_zero D T S i j b h
    refine ⟨?_, ?_⟩
    · have : BsupT D T S i j b = ⊥ := (Submodule.eq_bot_iff _).mpr fun z _ => hz z
      rw [this]; exact Submodule.fg_bot
    · exact Submodule.eq_top_iff'.mpr fun z => by rw [hz z]; exact Submodule.zero_mem _
  obtain ⟨T0, hT, hMK, hWK⟩ := In.mk_fg j h.1 h.2
  have hmem : ∀ t ∈ T0, t ∈ WKr D S j := fun t ht => by
    rw [WKr_of D S h.1 h.2]; exact (hMK t (hT t ht)).1
  let g : ↥T0 → FmT D T S i j b := fun t =>
    ((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨t.1, hmem t.1 t.2⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j))
  have hgB : Set.range g ⊆ BsupT D T S i j b := by
    rintro _ ⟨t, rfl⟩
    exact Submodule.subset_span ⟨⟨t.1, hmem t.1 t.2⟩, hT t.1 t.2, rfl⟩

  have hO : ∀ y ∈ Submodule.span (𝓞 S.Ks) (T0 : Set (S.WL j)), y ∈ WKr D S j ∧ ∀ hy : y ∈ WKr D S j,
      (((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨y, hy⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : FmT D T S i j b) ∈
        Submodule.span (T.O i) (Set.range g) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨hmem t ht, fun _ => Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩⟩
    | zero =>
      refine ⟨Submodule.zero_mem _, fun hy => ?_⟩
      have : (⟨0, hy⟩ : ↥(WKr D S j)) = 0 := rfl
      rw [this, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨Submodule.add_mem _ hy.1 hz.1, fun hyz => ?_⟩
      have : (⟨y + z, hyz⟩ : ↥(WKr D S j)) = ⟨y, hy.1⟩ + ⟨z, hz.1⟩ := rfl
      rw [this, TensorProduct.tmul_add]
      exact Submodule.add_mem _ (hy.2 hy.1) (hz.2 hz.1)
    | smul a y _ hy =>
      have hay : a • y = (a : S.Ks) • y := (algebraMap_smul S.Ks a y).symm
      have hm : a • y ∈ WKr D S j := by rw [hay]; exact Submodule.smul_mem _ _ hy.1
      refine ⟨hm, fun hy' => ?_⟩
      have : (⟨a • y, hy'⟩ : ↥(WKr D S j)) = (a : S.Ks) • ⟨y, hy.1⟩ := Subtype.ext hay
      rw [this, one_tmul_smul]
      obtain ⟨o, ho⟩ := ksInt_mem D T S i b a
      rw [← ho]
      exact Submodule.smul_mem _ o (hy.2 hy.1)
  have hBeq : BsupT D T S i j b = Submodule.span (T.O i) (Set.range g) := by
    refine le_antisymm ?_ (Submodule.span_le.mpr hgB)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (hO x.1 (hMK x.1 hx).2).2 x.2
  refine ⟨?_, ?_⟩
  · rw [hBeq]; exact Submodule.fg_span (Set.finite_range g)

  have hK : ∀ y ∈ Submodule.span S.Ks (T0 : Set (S.WL j)), y ∈ WKr D S j ∧ ∀ hy : y ∈ WKr D S j,
      (((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨y, hy⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : FmT D T S i j b) ∈
        Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨hmem t ht, fun _ => Submodule.subset_span (hgB ⟨⟨t, ht⟩, rfl⟩)⟩
    | zero =>
      refine ⟨Submodule.zero_mem _, fun hy => ?_⟩
      have : (⟨0, hy⟩ : ↥(WKr D S j)) = 0 := rfl
      rw [this, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨Submodule.add_mem _ hy.1 hz.1, fun hyz => ?_⟩
      have : (⟨y + z, hyz⟩ : ↥(WKr D S j)) = ⟨y, hy.1⟩ + ⟨z, hz.1⟩ := rfl
      rw [this, TensorProduct.tmul_add]
      exact Submodule.add_mem _ (hy.2 hy.1) (hz.2 hz.1)
    | smul c y _ hy =>
      have hm : c • y ∈ WKr D S j := Submodule.smul_mem _ _ hy.1
      refine ⟨hm, fun hy' => ?_⟩
      have : (⟨c • y, hy'⟩ : ↥(WKr D S j)) = c • ⟨y, hy.1⟩ := rfl
      rw [this, one_tmul_smul]
      exact Submodule.smul_mem _ _ (hy.2 hy.1)
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  change KT D T i b ⊗[S.Ks] ↥(WKr D S j) at z
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul k m =>
    have hm : (m : S.WL j) ∈ Submodule.span S.Ks (T0 : Set (S.WL j)) := by
      exact hWK _ ((WKr_of D S h.1 h.2).le m.2)
    have h1 := (hK m.1 hm).2 m.2
    have h2 : (k ⊗ₜ[S.Ks] m : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = k • ((1 : KT D T i b) ⊗ₜ[S.Ks] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ k h1
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem bsupT_fg_span_all : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤ :=
  fun D S In T i j b => bsupT_fg_span D T S In i j b

end GlobalTheory.HeightCounting.FormsStep
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem eIdem_all : ∀ D : D7, EIdem D := by
  intro D
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  let φ : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp (algebraMap ↥D.LL0 D.what₂.LL)
  have hφ : Function.Injective φ := φ.injective
  let M := MonoidAlgebra.mapRingHom (G0g D.nd) φ
  have hM : Function.Injective M := by
    intro x y h
    refine MonoidAlgebra.ext (Finsupp.ext fun g => hφ ?_)
    have := congrArg (fun z => z.coeff g) h
    simpa [M, MonoidAlgebra.mapRingHom] using this
  have he : M (eL D) = D.ntypes.e0 := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    have := D.nStage_trivialCharacter_coeff_eq g
    simpa [M, eL, MonoidAlgebra.mapRingHom, φ] using this
  have hc : ∀ a, D.ntypes.e0 * a = a * D.ntypes.e0 := fun a => by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_comm _ a
  have hi : D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_mul_self _
  have hs : ∀ g : G0g D.nd, M (MonoidAlgebra.of _ _ g) = MonoidAlgebra.of _ _ g := fun g => by
    simp [M, MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom]
  refine ⟨hM ?_, fun g => hM ?_⟩
  · rw [map_mul, he, hi]
  · rw [map_mul, map_mul, he, hs, hc]

end GlobalTheory.HeightCounting.FormsStep
end
