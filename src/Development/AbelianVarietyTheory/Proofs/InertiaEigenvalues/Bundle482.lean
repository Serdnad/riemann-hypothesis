module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosocles
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle473
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle134
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle471
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle288
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle474
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle475
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.transport_keeps_products_cosocles : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (r N : ℕ) (x : Fin r → IrrGL (k := k)) (x' : Fin r → IrrGL (k := k')) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) (y : IrrRep (GL (Fin N) k)) (y' : IrrRep (GL (Fin N) k')), (∀ a, RepRel i (x a) (x' a)) → RepRel i (cls y) (cls y') → IsCosocle y.ρ (prodIrr x hd) → IsCosocle y'.ρ (prodIrr x' hd') := by
  first | exact @GlobalTheory.FieldTransport.isCosocle_prodIrr_transport | exact GlobalTheory.FieldTransport.isCosocle_prodIrr_transport | (intros; apply GlobalTheory.FieldTransport.isCosocle_prodIrr_transport <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.rec_unique_of_laws : LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w.adicCompletion E) → WD h) (ψ : AddChar (w.adicCompletion E) Circle) (e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ), Continuous ψ → ψ ≠ 1 → e ψ = e' ψ → LawsMin a ha e rc → LawsMin a ha e' rc' → rc = rc' := by
  first | exact @GlobalTheory.LocLanglands.Unique.eq_of_lawsMin | exact GlobalTheory.LocLanglands.Unique.eq_of_lawsMin | (intros; apply GlobalTheory.LocLanglands.Unique.eq_of_lawsMin <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment : ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k)), IsL 𝔪 x.rep → HasSupport x.rep (msupp 𝔪) := by
  first | exact @GlobalTheory.LocGL.hasSupport_msupp_of_isL | exact GlobalTheory.LocGL.hasSupport_msupp_of_isL | (intros; apply GlobalTheory.LocGL.hasSupport_msupp_of_isL <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.ProdReorder

namespace GlobalTheory.ProdFlatten

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure BR (k : Type) [Field k] (n : ℕ) : Type 1 where

  V : Type
  [ac : AddCommGroup V]
  [smul : Module ℂ V]

  ρ : Representation ℂ (GL (Fin n) k) V

attribute [instance] BR.ac BR.smul

def one (w : IrrGL (k := k)) : BR k w.1 := ⟨_, w.rep⟩

def two {r t N : ℕ} (e : r + t = N) (A : BR k r) (C : BR k t) : BR k N :=
  ⟨_, ind₂ (stdSum e) (extTensor A.ρ C.ρ)⟩

def mp {d M : ℕ} (N : Fin d → ℕ) (hM : ∑ i, N i = M) (A : ∀ i, BR k (N i)) : BR k M :=
  ⟨_, multiProd (stdBlocks N hM) fun i => (A i).ρ⟩

def pr {a N : ℕ} (x : Fin a → IrrGL (k := k)) (hx : ∑ i, (x i).1 = N) : BR k N :=
  mp (fun i => (x i).1) hx fun i => one (x i)

def Iso {n : ℕ} (A C : BR k n) : Prop := Nonempty (A.ρ.Equiv C.ρ)

def Sm {n : ℕ} (A : BR k n) : Prop := IsSmooth A.ρ

theorem iso_refl {n : ℕ} (A : BR k n) : Iso A A := eqv_refl A.ρ

theorem iso_symm {n : ℕ} {A C : BR k n} (h : Iso A C) : Iso C A := eqv_symm (ρ := A.ρ) (σ := C.ρ) h

theorem iso_trans {n : ℕ} {A C D : BR k n} (h : Iso A C) (h' : Iso C D) : Iso A D :=
  eqv_trans (ρ := A.ρ) (σ := C.ρ) (τ := D.ρ) h h'

theorem sm_one (w : IrrGL (k := k)) : Sm (one w) := w.2.rep.smooth

theorem sm_pr {a N : ℕ} (x : Fin a → IrrGL (k := k)) (hx : ∑ i, (x i).1 = N) : Sm (pr x hx) := isSmooth_prodIrr x hx

theorem two_congr {r t N : ℕ} (e : r + t = N) {A A' : BR k r} {C C' : BR k t} (h : Iso A A') (h' : Iso C C') :
    Iso (two e A C) (two e A' C') :=
  ind₂_congr e (π₁ := A.ρ) (σ₁ := A'.ρ) (π₂ := C.ρ) (σ₂ := C'.ρ) h h'

theorem two_assoc {r s t M M' N : ℕ} (h₁ : r + s = M) (h₂ : M + t = N) (h₃ : s + t = M') (h₄ : r + M' = N)
    (A : BR k r) (C : BR k s) (D : BR k t) (s₁ : Sm A) (s₂ : Sm C) (s₃ : Sm D) :
    Iso (two h₂ (two h₁ A C) D) (two h₄ A (two h₃ C D)) :=
  ind₂_assoc' h₁ h₂ h₃ h₄ A.ρ C.ρ D.ρ s₁ s₂ s₃

theorem mp_head {d T M : ℕ} (N : Fin (d + 1) → ℕ) (hM : ∑ i, N i = M) (A : ∀ i, BR k (N i))
    (hT : ∑ i : Fin d, N i.succ = T) (e : N 0 + T = M) :
    Iso (mp N hM A) (two e (A 0) (mp (fun i : Fin d => N i.succ) hT fun i => A i.succ)) :=
  multiProd_head (d := N) (X := fun i => (A i).V) (fun i => (A i).ρ) (stdBlocks N hM) e
    (stdBlocks (fun i : Fin d => N i.succ) hT)

theorem two_unit {r t : ℕ} (e : r + t = r) (A : BR k r) (hA : Sm A) (N : Fin 0 → ℕ) (hN : ∑ i, N i = t)
    (C : ∀ i, BR k (N i)) : Iso (two e A (mp N hN C)) A :=
  ind₂_unit_right e A.ρ hA (d := N) (X := fun i => (C i).V) (fun i => (C i).ρ) (stdBlocks N hN)

theorem two_unit_pr {r t : ℕ} (e : r + t = r) (A : BR k r) (hA : Sm A) (y : Fin 0 → IrrGL (k := k))
    (hy : ∑ i, (y i).1 = t) : Iso (two e A (pr y hy)) A :=
  two_unit e A hA _ hy _

theorem pr_succ {a t N : ℕ} (z : Fin (a + 1) → IrrGL (k := k))
    (hx : ∑ i : Fin a, (z i.succ).1 = t) (hz : ∑ i, (z i).1 = N) (e : (z 0).1 + t = N) :
    Iso (pr z hz) (two e (one (z 0)) (pr (fun i : Fin a => z i.succ) hx)) :=
  mp_head (fun i => (z i).1) hz (fun i => one (z i)) hx e

theorem of_iso {d h : ℕ} (y : Fin d → Fin h → IrrGL (k := k)) (N : Fin d → ℕ) {M c : ℕ} (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M) (z : Fin c → IrrGL (k := k)) (hz : ∑ p, (z p).1 = M)
    (H : Iso (mp N hM fun i => pr (y i) (hN i)) (pr z hz)) :
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv (prodIrr z hz)) := H

attribute [irreducible] one two mp pr Iso Sm

theorem pr_congr {a b N : ℕ} {x : Fin a → IrrGL (k := k)} {z : Fin b → IrrGL (k := k)} (h : List.ofFn x = List.ofFn z)
    (hx : ∑ i, (x i).1 = N) (hz : ∑ i, (z i).1 = N) : Iso (pr x hx) (pr z hz) := by
  obtain rfl : a = b := by simpa using congrArg List.length h
  obtain rfl := List.ofFn_injective h
  exact iso_refl _

theorem pr_cons {a b t N : ℕ} {w : IrrGL (k := k)} {x : Fin a → IrrGL (k := k)} {z : Fin b → IrrGL (k := k)}
    (h : List.ofFn z = w :: List.ofFn x) (hx : ∑ i, (x i).1 = t) (hz : ∑ i, (z i).1 = N) (e : w.1 + t = N) :
    Iso (pr z hz) (two e (one w) (pr x hx)) := by
  have hb : b = a + 1 := by simpa using congrArg List.length h
  subst hb
  have h' : z 0 :: List.ofFn (fun i : Fin a => z i.succ) = w :: List.ofFn x := List.ofFn_succ.symm.trans h
  have h₁ : z 0 = w := (List.cons.inj h').1
  have h₂ : (fun i : Fin a => z i.succ) = x := List.ofFn_injective (List.cons.inj h').2
  subst h₁ h₂
  exact pr_succ z hx hz e

theorem pr_append {a : ℕ} : ∀ {b c r t N : ℕ} (x : Fin a → IrrGL (k := k)) (y : Fin b → IrrGL (k := k)) (z : Fin c → IrrGL (k := k))
    (_ : List.ofFn z = List.ofFn x ++ List.ofFn y) (_ : a ≠ 0 ∨ b = 0) (hx : ∑ i, (x i).1 = r)
    (hy : ∑ i, (y i).1 = t) (hz : ∑ i, (z i).1 = N) (e : r + t = N),
    Iso (pr z hz) (two e (pr x hx) (pr y hy)) := by
  induction a with
  | zero =>
    intro b c r t N x y z h hab hx hy hz e
    obtain rfl : b = 0 := by simpa using hab
    obtain rfl : t = 0 := by simpa using hy.symm
    have e0 : N = r := e.symm
    subst e0
    exact iso_trans (pr_congr (by simpa using h) hz hx) (iso_symm (two_unit_pr e _ (sm_pr x hx) y hy))
  | succ a ih =>
    intro b c r t N x y z h _ hx hy hz e
    have hx' : List.ofFn x = x 0 :: List.ofFn fun i : Fin a => x i.succ := List.ofFn_succ
    have hs : (x 0).1 + ∑ i : Fin a, (x i.succ).1 = r := (Fin.sum_univ_succ fun i => (x i).1).symm.trans hx
    have A := pr_cons hx' rfl hx hs
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · obtain rfl : (x 0).1 = r := by simpa using hs
      have B := iso_trans A (two_unit_pr hs _ (sm_one (x 0)) (fun i : Fin 0 => x i.succ) rfl)
      refine iso_trans (pr_cons (w := x 0) (by simpa using h) hy hz e) ?_
      exact two_congr e (iso_symm B) (iso_refl _)
    · let L := (List.ofFn fun i : Fin a => x i.succ) ++ List.ofFn y
      have hL : List.ofFn L.get = L := List.ofFn_get L
      have hT : ∑ i, (L.get i).1 = ∑ i : Fin a, (x i.succ).1 + t := by
        have := congrArg (fun l : List (IrrGL (k := k)) => (l.map Sigma.fst).sum) hL
        simp only [L, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn, Function.comp_def] at this
        rw [← hy]
        exact this
      have e' : (x 0).1 + (∑ i : Fin a, (x i.succ).1 + t) = N := by omega
      have B := pr_cons (w := x 0) (z := z) (x := L.get) (by rw [h, hx', hL]; rfl) hT hz e'
      have C := ih (fun i => x i.succ) y L.get hL (Or.inl ha.ne') rfl hy hT rfl
      have D := two_assoc hs e rfl e' (one (x 0)) (pr (fun i : Fin a => x i.succ) rfl) (pr y hy)
        (sm_one _) (sm_pr _ _) (sm_pr _ _)
      exact iso_trans B (iso_trans (two_congr e' (iso_refl _) C) (iso_trans (iso_symm D)
        (two_congr e (iso_symm A) (iso_refl _))))

end GlobalTheory.ProdFlatten
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.CharSplit

theorem admissibleCocycle_negCharPower_mem_coboundaries : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 1 ≤ e → e < Dt.t → ∀ z ∈ M.twistedModelAdmissibleCocycles (chr (M.ω ^ (-e))), z ∈ cob (chr (M.ω ^ (-e))) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 e he1 het z hz
  obtain ⟨N, b, g, hmod, hrep, hzz⟩ := GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 _ z hz
  have hN : N = M.Nχ e := GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 e (by omega) het N hmod
  subst hN
  apply GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F _ z b g hrep

  have hlat := fun i => M.χ_lat e (by omega) het i

  set J : ZMod n → ℕ := fun i =>
    if Dt.ty i = LType.G then (Dt.w i).toNat else (Dt.wst i - e).toNat with hJ
  have hJG : ∀ i, Dt.ty i = LType.G → J i = (Dt.w i).toNat := fun i h => by simp [hJ, h]
  have hJB : ∀ i, Dt.ty i = LType.Bd → J i = (Dt.wst i - e).toNat := fun i h => by simp [hJ, h]

  have hsmall : ∀ i (j : ℕ), j ≤ J i → e + (j : ℤ) < l := by
    intro i j hj
    have hT := h1 i
    have hw := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
    cases hty : Dt.ty i with
    | G =>
      obtain ⟨-, -, hw1, hw2⟩ := hw.2.2.1 hty
      rw [hJG i hty] at hj
      omega
    | Bd =>
      obtain ⟨-, -, hb1, hb2⟩ := hw.2.2.2 hty
      rw [hJB i hty] at hj
      omega
  obtain ⟨m, -, hm⟩ := GlobalTheory.PhiGam.cocycle_split_of_contracting R (F.D (chr (M.ω ^ (-e)))) (M.Nχ e) J
    (fun i => (hlat i).1) (fun i => (hlat i).2.1)
    (fun i => by rw [(hlat i).2.2.1]; exact sh_le_sh_of_le he1 _)
    (fun i j hj1 hjJ => by
      rw [(hlat i).2.2.2]
      unfold resCount
      classical
      simp only [Multiset.card_eq_zero, Multiset.filter_eq_nil, Multiset.mem_singleton, forall_eq]
      intro hcast
      have h0 : ((e + (j : ℤ) : ℤ) : k) = 0 := by
        push_cast at hcast ⊢
        linear_combination hcast
      rw [CharP.intCast_eq_zero_iff k l] at h0
      have hle := Int.le_of_dvd (by omega) h0
      have := hsmall i j hjJ
      omega)
    b g (fun i => (hzz i).1) (fun i => (hzz i).2.1)
    (fun i => by
      have hw := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
      cases hty : Dt.ty i with
      | G =>
        have hb := (hzz i).2.2.1 hty
        have h := (hw.2.2.1 hty).2.2.1
        have hJi : ((J i : ℕ) : ℤ) = Dt.w i := by
          rw [hJG i hty]
          omega
        rw [hJi]
        exact hb
      | Bd =>
        have hb := ((hzz i).2.2.2 hty).1
        have h := (hw.2.2.2 hty).2.2.1
        rw [(hlat i).2.2.1, sh_sh_eq] at hb
        have hJi : -((J i : ℕ) : ℤ) = -Dt.wst i + e := by
          rw [hJB i hty]
          omega
        rw [hJi]
        exact hb)
  rw [herrB_eq_range]
  refine ⟨m, ?_⟩
  rw [herrD_apply]
  exact Prod.ext (funext fun i => ((hm i).1).symm) (funext fun i => ((hm i).2).symm)

end GlobalTheory.CharSplit
end

section

open Matrix Formalism.IndefR.Datum GlobalTheory.ExportSeries

namespace GlobalTheory

theorem dU_eq_const_mul_det_topL_translate :
  ∀ (k : Type) [Field k] (r n : ℕ) (β : DetBases k r n) (U : Planes k r n),
  ∃ (g : GL (Fin n) k) (c : kˣ), ∀ y : Matrix (Fin r) (Fin n) k,
    dU β U y = (c : k) * (topL r (y * (g : Matrix (Fin n) (Fin n) k))).det := by
  intro k _ r n β U
  have hrn : r ≤ n := by have := U.2; omega
  let b := Module.finBasisOfFinrankEq k _ (finrank_quot U)
  have hU : Module.finrank k U.1 = n - r := by have := U.2; omega
  let bU := Module.finBasisOfFinrankEq k U.1 hU
  obtain ⟨lam, hlam⟩ := LinearMap.exists_extend (bU.equivFun.toLinearMap)
  let φ : (Fin n → k) →ₗ[k] (Fin n → k) := LinearMap.pi fun j =>
    if h : j.val < r then (LinearMap.proj (⟨j.val, h⟩ : Fin r)) ∘ₗ b.equivFun.toLinearMap ∘ₗ U.1.mkQ
    else (LinearMap.proj (⟨j.val - r, by have := j.2; omega⟩ : Fin (n - r))) ∘ₗ lam
  have hφ1 : ∀ v (i : Fin r), φ v ⟨i.val, by omega⟩ = b.repr (U.1.mkQ v) i := by
    intro v i
    simp [φ, i.2]
  have hφ2 : ∀ v (i : Fin (n - r)), φ v ⟨r + i.val, by omega⟩ = lam v i := by
    intro v i
    simp [φ]
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : U.1.mkQ v = 0 := by
      apply b.repr.injective
      ext i
      have := hφ1 v i
      rw [hv] at this
      simpa using this.symm
    have hvU : v ∈ U.1 := by simpa using h1
    have h2 : bU.equivFun ⟨v, hvU⟩ = 0 := by
      have e : lam v = bU.equivFun ⟨v, hvU⟩ := by
        have := LinearMap.congr_fun hlam ⟨v, hvU⟩
        simpa using this
      rw [← e]
      ext i
      have := hφ2 v i
      rw [hv] at this
      simpa using this.symm
    have : (⟨v, hvU⟩ : U.1) = 0 := bU.equivFun.injective (by rw [h2, map_zero])
    simpa using congrArg Subtype.val this

  let ψ := LinearEquiv.ofInjectiveEndo φ hφ
  let A : Matrix (Fin n) (Fin n) k := (LinearMap.toMatrix' φ)ᵀ
  let B : Matrix (Fin n) (Fin n) k := (LinearMap.toMatrix' ψ.symm.toLinearMap)ᵀ
  have hAB : A * B = 1 := by
    have hc : ψ.symm.toLinearMap ∘ₗ φ = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      show ψ.symm (ψ v) = v
      exact ψ.symm_apply_apply v
    simp only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]
  have hBA : B * A = 1 := by
    have hc : φ ∘ₗ ψ.symm.toLinearMap = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      show ψ (ψ.symm v) = v
      exact ψ.apply_symm_apply v
    simp only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]
  let g : GL (Fin n) k := ⟨A, B, hAB, hBA⟩
  have hb : β.form U b ≠ 0 := fun h0 => β.ne U (by rw [(β.form U).eq_smul_basis_det b, h0, zero_smul])
  refine ⟨g, Units.mk0 _ hb, fun y => ?_⟩
  have key : ∀ i j, (y * A) i j = φ (y.row i) j := by
    intro i j
    rw [← congrFun (LinearMap.toMatrix'_mulVec φ (y.row i)) j]
    simp [A, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm, Matrix.row]
  have ht : topL r (y * (g : Matrix (Fin n) (Fin n) k)) = (b.toMatrix fun i => U.1.mkQ (y.row i))ᵀ := by
    ext i j
    have hj : j.val < n := by omega
    have e1 : topL r (y * (g : Matrix (Fin n) (Fin n) k)) i j = (y * A) i ⟨j.val, hj⟩ := by
      simp [topL, hj, g]
    rw [e1, key, hφ1 (y.row i) j, transpose_apply, Module.Basis.toMatrix_apply]
  rw [ht, det_transpose, ← Module.Basis.det_apply, dU]
  conv_lhs => rw [(β.form U).eq_smul_basis_det b]
  rfl

end GlobalTheory
end

section

open Matrix GlobalTheory.ExportSeries

namespace GlobalTheory.ExportSeries

theorem sum_univCoef_eq_prim : ∀ (k C : Type) [Field k] [Finite k] [AddCommGroup C] [Fintype C] (r n : ℕ), r ≤ n →
    ∀ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k), ∑ c, univCoef β κ c y = prim y := by
  intro k C _ _ _ _ r n hrn β κ y
  classical
  letI := Fintype.ofFinite (Planes k r n)

  have hterm : ∀ U : Planes k r n, ∑ c, (univTerm β κ y U).coeff c = if Compl U.1 y then 1 else 0 := by
    intro U
    unfold univTerm
    by_cases h : Compl U.1 y
    · rw [dite_eq_left h, if_pos h]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    · rw [dite_eq_right h, if_neg h]
      simp
  have hsum : ∑ c, univCoef β κ c y = ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ *
      (Nat.card {U : Planes k r n // Compl U.1 y} : ℚ) := by
    simp only [univCoef, univ, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun U _ => hterm U, Finset.sum_boole]
    congr 2
    rw [Nat.card_eq_fintype_card (α := {U : Planes k r n // Compl U.1 y}), Fintype.card_subtype]
  rw [hsum]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have ht : r + t - r = t := by omega
  rw [ht]
  set R := Submodule.span k (Set.range y.row) with hR
  have hRle : Module.finrank k R ≤ r := by
    have := finrank_range_le_card (R := k) y.row
    rw [Fintype.card_fin] at this
    exact this
  have hcard : Nat.card {U : Planes k r (r + t) // Compl U.1 y} =
      Nat.card {U : Submodule k (Fin (r + t) → k) // Module.finrank k U = t ∧ R ⊔ U = ⊤} := by
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ (fun U => Compl U y)).trans
      (Equiv.subtypeEquivRight fun U => ?_))
    simp only [Compl, hR]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [hcard, GlobalTheory.card_subspaces_sup_eq_top k r t R hRle]
  have hq : ((Nat.card k : ℚ) ^ (r * t)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.card_pos.ne')
  have hli : LinearIndependent k y.row ↔ Module.finrank k R = r := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank, eq_comm]
  unfold prim
  by_cases h : Module.finrank k R = r
  · rw [if_pos h, if_pos (hli.2 h)]
    push_cast
    exact inv_mul_cancel₀ hq
  · rw [if_neg h, if_neg (fun h' => h (hli.1 h'))]
    simp

end GlobalTheory.ExportSeries
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

theorem _root_.GlobalTheory.T.fundamentalTwoCocycle_multiple_not_coboundary : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (a : O) (f : G → O), Continuous f → (∀ g h : G, d1 (twist ε O) f (g, h) = a * φ (c (g, h))) → a = 0 := by
  first | exact @GlobalTheory.TateNat.free_inj | exact GlobalTheory.TateNat.free_inj | (intros; apply GlobalTheory.TateNat.free_inj <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

theorem _root_.GlobalTheory.T.twoCocycle_fundamental_multiple_mod_pow : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → ∃ a : O, ∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h))) := by
  first | exact @GlobalTheory.UnifSpan.span_mod_pow | exact GlobalTheory.UnifSpan.span_mod_pow | (intros; apply GlobalTheory.UnifSpan.span_mod_pow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.continuous_twoCocycle_multiple_of_fundamental : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ : G →* ℤ_[l]ˣ) (c : G × G → ℤ_[l]), Continuous (fun g => (χ g : ℤ_[l])) → (∀ r, GlobalTheory.TateTop.Gen χ r c) → (∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)))) → (Continuous (fun p => (c p : ℚ_[l])) ∧ ∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * (c (h, k) : ℚ_[l]) - (c (g * h, k) : ℚ_[l]) + (c (g, h * k) : ℚ_[l]) - (c (g, h) : ℚ_[l]) = 0) ∧ ∀ z : G × G → ℚ_[l], Continuous z → (∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ (x : ℚ_[l]) (f : G → ℚ_[l]), Continuous f ∧ ∀ g h, ((χ g : ℤ_[l]) : ℚ_[l]) * f h - f (g * h) + f g = z (g, h) - x * (c (g, h) : ℚ_[l]) := by
  first | exact @GlobalTheory.GenSpan.span | exact GlobalTheory.GenSpan.span | (intros; apply GlobalTheory.GenSpan.span <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_fundamentalTwoCocycle_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), CompactSpace ↥(GK K) ∧ ∃ (χ : ↥(GK K) →* ℤ_[l]ˣ) (c : ↥(GK K) × ↥(GK K) → ℤ_[l]), Continuous (fun g => (χ g : ℤ_[l])) ∧ (∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])) ∧ (∀ r, GlobalTheory.TateTop.Gen χ r c) ∧ ∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ))) := by
  first | exact @GlobalTheory.TateTop.exists_fundamental_cocycle_loc | exact GlobalTheory.TateTop.exists_fundamental_cocycle_loc | (intros; apply GlobalTheory.TateTop.exists_fundamental_cocycle_loc <;> assumption)
end
