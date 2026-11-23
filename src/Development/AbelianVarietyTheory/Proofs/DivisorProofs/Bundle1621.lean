module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle124
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle132
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightParameterMemUnitInterval
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore

theorem mulPow_mulVar {K : Type} [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K) {a j l : ℕ}
    (h : j + (a + 1) = l) (h' : (j + 1) + a = l) (α : MonoDeg (Fin G.D) a) (i : Fin G.D) (m : G.Sec j) :
    mulPow G s h (MonoDeg.mulVar i α) m = mulPow G s h' α (G.mulW j (s i) m) := by
  rw [G.mulW_apply]
  unfold mulPow
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, monoVal_mulVar, mul_comm (secGer _ _ _ _ _), mul_assoc]

theorem filMono_of_kerRes : KerRes → FilMono := by
  intro H K _ _ G hnef hbig s hs a
  induction a with
  | zero =>
    intro j l h _ f hf
    obtain rfl : j = l := h
    have : Subsingleton (MonoDeg (Fin G.D) 0) := ⟨fun α β => Subtype.ext
      (((Finsupp.degree_eq_zero_iff _).1 α.2).trans ((Finsupp.degree_eq_zero_iff _).1 β.2).symm)⟩
    refine ⟨fun _ => f, fun _ => hf.1, ?_⟩
    rw [Fintype.sum_subsingleton _ (⟨0, rfl⟩ : MonoDeg (Fin G.D) 0)]
    exact (mulMono_zero _ _ _ _ _ f).symm
  | succ a ih =>
    classical
    intro j l h hj f hf
    have h' : (j + 1) + a = l := by omega
    have hfa : f ∈ Fil (G.ideal s) a (G.global l) := Fil_anti (Nat.le_succ a) hf
    obtain ⟨m, hm, e⟩ := ih (j + 1) l h' (by omega) f hfa
    have h0 : hs.sym h' (G.global l) ⟨f, hfa⟩ = 0 := (sym_eq_zero_iff _ _ _ _ _ _ _ _ _ _ _).2 hf
    have h1 : hs.sym h' (G.global l) ⟨f, hfa⟩ = fun α => hs.res (j + 1) (m α) :=
      sym_sum _ _ _ _ _ _ _ _ _ _ m _ e
    have hv : ∀ α, m α ∈ Fil (G.ideal s) 1 (G.global (j + 1)) := fun α =>
      ⟨hm α, (Res_eq_zero_iff _ _ _ _ _ _ _ _ _ _).1 (congrFun (h1.symm.trans h0) α)⟩
    choose m' hm' e' using fun α => H K G hnef hbig s hs j (by omega) (m α) (hv α)
    refine ⟨fun γ => ∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ),
      m' p.1 p.2, fun γ => sum_mem fun p _ => hm' _ _, ?_⟩
    have key : ∀ γ : MonoDeg (Fin G.D) (a + 1), mulPow G s h γ
        (∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ), m' p.1 p.2) =
        ∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ),
          mulPow G s h' p.1 (G.mulW j (s p.2) (m' p.1 p.2)) := fun γ => by

      rw [map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← (Finset.mem_filter.1 hp).2, mulPow_mulVar G s h h']
    rw [Finset.sum_congr rfl fun γ _ => key γ, Finset.sum_fiberwise, Fintype.sum_prod_type, e]
    refine Finset.sum_congr rfl fun α _ => ?_

    rw [e' α, map_sum]

end GlobalTheory.HSCore
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.BigOn.Inhab

namespace GlobalTheory.BigOn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem level_of_is {T : Core D} (hT : LawsM T) {Lc : LevCh D T0} {μ0 : T0} (hL : Lc.Is μ0) (hO : T.pb = Lc.C.P.pb) :
    T.Q.l.Mb = ∏ PP ∈ Lc.Pg, PP.asIdeal := by
  have hprod := T.Q.l.prod
  refine GlobalTheory.CoverHalf.eq_prod_of_squarefree ?_ _ fun PP => ?_
  · rw [hT.pins.2.1.1] at hprod
    exact (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (T.Q.l.Mb * _)).of_mul_left
  · rw [hL.Pg, hT.half.2, GlobalTheory.CoverHalf.prod_map_le_iff, hO]
    rfl

theorem exists_half_of_is {Lc : LevCh D T0} {μ0 : T0} (hL : Lc.Is μ0) {p : ℕ} (hp : p = D.host.pde ∨ p = D.host.pde') :
    ∃ P : HeightOneSpectrum (𝓞 D.host.K), (p : 𝓞 D.host.K) ∈ P.asIdeal ∧ ∀ t, ∀ PP ∈ Lc.Q t, (p : 𝓞 D.host.E) ∈ PP.asIdeal →
      P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
  obtain ⟨P, hP⟩ := hL.Q_de p hp
  by_cases h : ∃ t, ∃ PP ∈ Lc.Q t, (p : 𝓞 D.host.E) ∈ PP.asIdeal
  · obtain ⟨t, PP, h1, h2⟩ := h
    refine ⟨P, ?_, fun t PP h1 h2 => ?_⟩
    · rw [← hP t PP h1 h2]
      change algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (p : 𝓞 D.host.K) ∈ PP.asIdeal
      rwa [map_natCast]
    · rw [← hP t PP h1 h2]
      exact Ideal.map_comap_le
  · have hpp : p.Prime := by
      rcases hp with rfl | rfl
      exacts [D.host.pde_prime, D.host.pde'_prime]
    obtain ⟨P', hP'⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K hpp
    exact ⟨P', hP', fun t PP h1 h2 => absurd ⟨t, PP, h1, h2⟩ h⟩

theorem ownAt_special (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ownAt D v = D.host.pde ∨ ownAt D v = D.host.pde' := by
  unfold ownAt
  split_ifs
  exacts [Or.inr rfl, Or.inl rfl]

theorem oneHalf_of_is {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {μ0 : T0}
    (hL : R.toLevCh.Is μ0) : ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v,
      ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧ ∀ PP ∈ GlobalTheory.OnTies.placesOver R (R.mu v) (ownAt D v),
        (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
  classical
  choose P h1 h2 using fun (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde') => exists_half_of_is hL hp
  refine ⟨fun p => if hp : p = D.host.pde ∨ p = D.host.pde' then P p hp else R.C.P.pb 0, fun v => ?_⟩
  simp only [dif_pos (ownAt_special v)]
  refine ⟨h1 _ _, fun PP hPP => ?_⟩
  have h3 := Finset.mem_filter.1 hPP
  exact h2 _ _ _ PP h3.1 h3.2

theorem level_and_oneHalf (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (μ0 : T0) (hL : R.toLevCh.Is μ0)
    (hO : J.pb = R.C.P.pb) (hc : LawsCore J.toCore) :
    J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧
      ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v ∈ R.twPl, ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧
        ∀ PP ∈ GlobalTheory.OnTies.placesOver R (R.mu v) (ownAt D v),
          (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal :=
  ⟨level_of_is hc.toLawsM hL hO, (oneHalf_of_is R hL).imp fun _ h v _ => h v⟩

theorem coreTies_of_is {L : SizeData₂ D} {EX : ErrX D} {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {μ0 : T0}
    (hL : R.toLevCh.Is μ0) (hO : J.pb = R.C.P.pb) (hc : LawsCore J.toCore) (hcan : J.Q.Canon)
    (hr : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) (hE : HalfEX J.toCore EX) (h₁ : FieldOK0 D D.host.pde)
    (h₂ : FieldOK0 D D.host.pde') (hs : FieldSmall D L) (hd : ∀ x, ((R.C.del.1 x : ℂˣ) : ℂ) ∈ FO D)
    (hd' : ∀ x, ((R.C.del'.1 x : ℂˣ) : ℂ) ∈ FO D) : CoreTies L EX J R :=
  ⟨hc, hcan, hr, hE, h₁, h₂, hs, (level_and_oneHalf J R μ0 hL hO hc).1, (level_and_oneHalf J R μ0 hL hO hc).2, hd, hd'⟩

end GlobalTheory.BigOn

end
end

section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.BigOn

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isLev_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.toLevCh.Is A.μ0) :
    (reScal R lam kap).toLevCh.Is A.μ0 := h

theorem isGrp_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsGrp F) :
    (reScal R lam kap).IsGrp F := { h with }

theorem isFam_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsFam) :
    (reScal R lam kap).IsFam := { h with }

theorem isModels_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsModels) :
    (reScal R lam kap).IsModels := { h with }

theorem isChain_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsChain) :
    (reScal R lam kap).IsChain := { h with }

theorem isThP_rescale (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsThP) :
    (reScal R lam kap).IsThP := { h with }

def reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) : CxData B :=
  { X with lam := lam, κ := κ }

theorem liftMatC_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) :
    (reScalCx X lam κ).liftMatC cr b j t = X.liftMatC cr b j t := rfl

theorem liftMat_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) :
    (reScalCx X lam κ).liftMat cr b j t = X.liftMat cr b j t :=
  congrArg (kMat Bs.v0.embedding) (liftMatC_reScalCx X lam κ cr b j t)

theorem iw_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) : ((reScalCx X lam κ).data cr b).Iw = (X.data cr b).Iw := by
  funext j t w
  exact congrArg (fun θ => idx w (X.M b j) (matLat θ ((lv (fc X.zs) b).Tl j t))) (liftMat_reScalCx X lam κ cr b j t)

theorem zs_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) : (reScalCx X lam κ).zs = X.zs := rfl


theorem toCx_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) :
    (reScal R lam kap).toCx F = reScalCx (R.toCx F) lam (fun _ => kap) := rfl

theorem reScal_nonzeroIndexPlace_iff (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : (reScal R lam kap).NonzeroIndexPlace F w ↔ R.NonzeroIndexPlace F w := by
  unfold RealDat.NonzeroIndexPlace
  rw [toCx_reScal, iw_reScalCx, zs_reScalCx]

theorem isTup_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsTup F) :
    (reScal R lam kap).IsTup F :=
  ⟨fun w hw => h.tw w ((reScal_nonzeroIndexPlace_iff R F lam kap w).1 hw), h.mu_off, h.mu_used, h.mu_ne, h.mu_conj, h.mu_on⟩

end

theorem char_charOf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → R.IsThP → R.IsTup F → (charOf R F).Char F := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h1 h2 h3 h4 h5 h6 h7
  obtain ⟨lam, kap, hs⟩ := GlobalTheory.ScalChoice.exists_isScal D G Pl0 T0 A Ks R F
  have hex : ∃ q : (type_of% R.lam) × ℝ, (reScal R q.1 q.2).Char F :=
    ⟨(lam, kap), isLev_reScal R lam kap h1, isGrp_reScal R F lam kap h2, isFam_reScal R lam kap h3,
      isModels_reScal R lam kap h4, isChain_reScal R lam kap h5, isThP_rescale R lam kap h6, hs,
      isTup_reScal R F lam kap h7⟩
  exact Classical.epsilon_spec hex

end GlobalTheory.BigOn
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.BigOn

theorem isLattice_of_spanK {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {C : Type}
    [AddCommGroup C] [Module F C] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (M : Submodule (𝓞 F) C) (h : IsLatIn ⊤ (spanK z (M : Set C))) :
    Submodule.IsFullLattice F M := by
  have hinj : Function.Injective (coordMap z) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : z.symm ((1 : K) ⊗ₜ[F] x) = 0 := hx
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff F C x).1 h1
  have hfg : M.FG := by
    have h1 : ((spanK z (M : Set C)).restrictScalars (𝓞 F)).FG := h.1.restrictScalars
    have h2 : M.map ((coordMap z).restrictScalars (𝓞 F)) ≤ (spanK z (M : Set C)).restrictScalars (𝓞 F) := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_spanK z hx
    exact Submodule.fg_of_fg_map_injective ((coordMap z).restrictScalars (𝓞 F)) hinj (h1.of_le h2)
  letI := Submodule.IsLattice.of_fg F hfg
  refine ⟨?_⟩
  · refine Submodule.baseChange_injective (A := K) ?_
    rw [Submodule.baseChange_top, Submodule.baseChange_span, eq_top_iff]
    intro y _
    have h2 := h.2
    unfold spanK at h2
    rw [Submodule.span_span_of_tower] at h2
    have h3 : z.symm y ∈ Submodule.span K ((fun f : C => z.symm (1 ⊗ₜ[F] f)) '' (M : Set C)) := h2 ▸ Submodule.mem_top
    have h4 := Submodule.mem_map_of_mem (f := z.toLinearMap) h3
    rw [Submodule.map_span, ← Set.image_comp] at h4
    simp only [Function.comp_def, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h4
    exact h4

theorem exists_rem_of_concl {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P6 j) (S : WeightAlgebra.Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (a b c d : ℝ)
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (hM : IsLatIn ⊤ (spanK z (B.Mlat j ka : Set _)))
    (hC : WeightAlgebra.Concl X S ka wL wF T nus (X.rk ka (B.Mlat j ka) * a * b * c * d)) :
    ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ (n : ℝ) * (a * b * c * d)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)) (e : ℕ), (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e →
        ∀ W : Submodule K (Fin n → K),
          (lix v (_root_.Formalism.EigenvalueLevelCeiling.cut W (spanK z (B.Mlat j ka : Set _))) (_root_.Formalism.EigenvalueLevelCeiling.cut W (spanK z {F | X.inc ka F ∈ X.Theta S ka wL wF T})) : ℝ) ≤
            ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  have hM' := isLattice_of_spanK z _ hM
  letI := hM'
  have hn : X.rk ka (B.Mlat j ka) = n := by
    unfold WeightAlgebra.PJ.rk
    rw [Submodule.IsFullLattice.span_eq_top, finrank_top]
    have := z.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_fin_fun] at this
    exact this.symm
  let Q : Formalism.MainNotions.Gaps.LocalGlobalPassage.Run D B P6 := ⟨j, X, S, ka, wL, wF, T, nus, X.rk ka (B.Mlat j ka) * a * b * c * d⟩
  letI : Submodule.IsFullLattice B.KO Q.M0 := hM'
  obtain ⟨r, h0, h1, h2, h3⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.l2 Q (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1 la)
    (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1b la) (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1c la) (by first | exact hM' | exact hM'.toIsLattice) hC
  have hβ : Q.β = (n : ℝ) * (a * b * c * d) := by
    change (X.rk ka (B.Mlat j ka) : ℝ) * a * b * c * d = _
    rw [hn]
    ring
  refine ⟨fun v => (v.asIdeal.ramificationIdx (𝓞 B.KO) : ℝ) * r (v.under (𝓞 B.KO)),
    fun v => mul_nonneg (Nat.cast_nonneg _) (h0 _),
    fun S' => (Formalism.MainNotions.Gaps.LocalGlobalPassage.l4 r h0 h1 S').trans (h2.trans hβ.le), ?_⟩
  intro v e he W
  have hpl : placeBelow (K := B.KO) v = v.under (𝓞 B.KO) := rfl
  have hram : ramOver (K := B.KO) v = v.asIdeal.ramificationIdx (𝓞 B.KO) := Formalism.MainNotions.Gaps.LocalGlobalPassage.ram_eq v
  obtain ⟨h4, h5⟩ := h3 (v.under (𝓞 B.KO))
  have hTh : Formalism.MainNotions.Gaps.LocalGlobalPassage.up (coordMap z) (Q.M0 ⊓ Q.Th0) ≤ spanK z {F | X.inc ka F ∈ X.Theta S ka wL wF T} :=
    Submodule.span_mono (Set.image_mono fun f hf => hf.2)
  exact Formalism.MainNotions.Gaps.LocalGlobalPassage.l5 (coordMap z) (coordMap_linearIndependent z) (coordMap_span z) Q.M0 (Q.M0 ⊓ Q.Th0) (Submodule.IsLattice.fg B.KO (B.Mlat j ka))
    Submodule.IsFullLattice.span_eq_top h4 inf_le_left v e (r (v.under (𝓞 B.KO))) (ramOver (K := B.KO) v * e)
    (by rw [hram]; push_cast; rfl) (h5 e (by rw [Int.cast_natCast, ← hpl]; exact he)) _ hTh W

theorem starRing_eq {R : Type} [CommRing R] (s t : StarRing R) (h : ∀ a : R, s.star a = t.star a) : s = t := by
  obtain @⟨@⟨@⟨⟨f⟩, _⟩, _⟩, _⟩ := s
  obtain @⟨@⟨@⟨⟨g⟩, _⟩, _⟩, _⟩ := t
  obtain rfl : f = g := funext h
  rfl

theorem exists_rem_of_tie {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} {X : WeightAlgebra.PJ D B P6 j}
    {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ} {ka wL wF : WeightFamilies.Wt D j} {T : ℕ}
    {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} {a b c d : ℝ}
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    {O : OnObj S P oc} {v₁ : HeightOneSpectrum (𝓞 K)} {i : Bs.J}
    {z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka} {act : P → B.Cusp j ka → B.Cusp j ka}
    (ht : FormTieK X hinj EX p ka wL wF T O v₁ i z act) (hM : IsLatIn ⊤ (O.Ms i))
    (hC : WeightAlgebra.Concl X (scalOfP B hinj EX p ka wL wF T) ka wL wF T nus (X.rk ka (B.Mlat j ka) * a * b * c * d)) :
    ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ (O.nZ i : ℝ) * (a * b * c * d)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)), FormTieK X hinj EX p ka wL wF T O v i z act →
        ∀ e : ℕ, (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e → ∀ W : Submodule K (Fin (O.nZ i) → K),
          (lix v (_root_.Formalism.EigenvalueLevelCeiling.cut W (O.Ms i)) (_root_.Formalism.EigenvalueLevelCeiling.cut W (O.Th v i)) : ℝ) ≤
            ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  obtain ⟨ρ, h0, h1, h2⟩ := exists_rem_of_concl X _ ka wL wF T nus a b c d z (ht.Ms_eq ▸ hM) hC
  refine ⟨ρ, h0, h1, fun v hv e he W => ?_⟩
  rw [hv.Ms_eq, hv.Th_eq]
  exact h2 v e he W

theorem nusR_le_eLam {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D)
    (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    letI := T.Q.H.starRing
    (Tp.TO : ℝ) * GlobalTheory.RunJoin.nusR h j (lR Tp hK j) la ≤
      ((GlobalTheory.RunDepth.depOf T.toCore EX Tp hK).Q.eLam (ramOverZ la)
        (nuStarAt (Xo := T.Q.Xo j) (c := T.Q.c) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) la j) (resCharOf la) : ℝ) := by
  have hn := GlobalTheory.RunDepthScale.nusOf_eq_ram_mul_nuStarAt D L Pm Tp hK T h EX j hj la
  refine le_trans (le_of_eq ?_) (DepPage.le_eLam _ _ _ _)
  refine (congrArg (fun t => (Tp.TO : ℝ) * t) hn).trans ?_
  rw [← mul_assoc, mul_comm (Tp.TO : ℝ)]
  rfl



theorem hasIndexBound_of_runs : ∀ CK : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → CoreTies L EX J R → OwnPin r → RunsHold Tp hK EX CK r → LeafSup O → LeafSpan O → O.b = L.sc.b → HasIndexBound O := by
  intro CK D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hO _ _ hR hS hSp hb
  obtain rfl : κ = fun i : Fin D.R.m => kaR Tp hK ((i : ℕ) + 1) := funext hO.kap
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hO.tied
  obtain ⟨st, hd⟩ := hO.depth
  let _ := hostAlg D
  obtain rfl : st = J.toCore.Q.H.starRing := starRing_eq _ _ hd.star_eq
  let _ := J.toCore.Q.H.starRing
  let _ : ∀ s : RunData J, Algebra s.full.J.Q.c.F D.what₂.LL := fun _ => inst
  let _ : ∀ (s : RunData J) (h : LawsP s.full.toTop), Algebra (recB h.toLawsCore).KO D.what₂.LL := fun _ _ => inst
  have key : ∀ (q : Prop) (i : Fin D.R.m), ∃ ρ : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ, (∀ v, 0 ≤ ρ v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)),
        ∑ v ∈ S', Formalism.DivisionValues.lw v * ρ v ≤ (O.nZ i : ℝ) * (D.R.f * D.R.m * L.sc.b * L.de2)) ∧
      ∀ v, (Formalism.EigenvalueLevelCeiling.plc v = D.host.pde ↔ q) → ∀ W : Submodule D.what₂.LL (Fin (O.nZ i) → D.what₂.LL),
        (lix v (_root_.Formalism.EigenvalueLevelCeiling.cut W (O.Ms i)) (_root_.Formalism.EigenvalueLevelCeiling.cut W (O.Th v i)) : ℝ) ≤ (O.E v i : ℝ) * (finrank D.what₂.LL W : ℝ) + ρ v := by
    intro q i
    by_cases hq : ∃ v₁ : HeightOneSpectrum (𝓞 D.what₂.LL), (Formalism.EigenvalueLevelCeiling.plc v₁ = D.host.pde ↔ q)
    · obtain ⟨v₁, hv₁⟩ := hq
      obtain ⟨ρ, h0, h1, h2⟩ := @exists_rem_of_tie D (recB hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inst _ _ _ _ _ _ _ _ _ _ _ _ (ht v₁ i).1.toFormTieK (hS i).1
        (hR v₁ (hO.ok.laws v₁).p hinj ((i : ℕ) + 1) (inR_succ i)).2
      refine ⟨ρ, h0, h1, fun v hv W => ?_⟩
      have e1 : r.used v = r.used v₁ := by
        unfold TwoRuns.used
        exact if_congr (hv.trans hv₁.symm) rfl rfl
      have e2 : ownAt D v = ownAt D v₁ := by
        unfold ownAt
        exact if_congr (hv.trans hv₁.symm) rfl rfl
      have h3 := (ht v i).1.toFormTieK
      have h4 := (hO.ok.laws v).p
      rw [hd.E_eq v i]
      refine h2 v ?_ _ (nusR_le_eLam Tp hK EX (r.used v₁).full.toTop (hO.ok.laws v₁).p _ (inR_succ i) _) W
      have h5 : ∀ (s : RunData J) (h' : LawsP s.full.toTop) (p' : ℕ), s = r.used v₁ → p' = ownAt D v₁ →
          letI : Algebra (recB h'.toLawsCore).KO D.what₂.LL := inst
          FormTieK (recPJ h' ((i : ℕ) + 1) (inR_succ i)) hinj EX p' (kaR Tp hK ((i : ℕ) + 1)) (lR Tp hK ((i : ℕ) + 1))
            (fR Tp hK ((i : ℕ) + 1)) Tp.TO O v i (z i) (act i) →
          letI : Algebra (recB (hO.ok.laws v₁).p.toLawsCore).KO D.what₂.LL := inst
          FormTieK (recPJ (hO.ok.laws v₁).p ((i : ℕ) + 1) (inR_succ i)) hinj EX (ownAt D v₁) (kaR Tp hK ((i : ℕ) + 1))
            (lR Tp hK ((i : ℕ) + 1)) (fR Tp hK ((i : ℕ) + 1)) Tp.TO O v i (z i) (act i) := by
        rintro _ _ _ rfl rfl h
        exact h
      exact h5 _ h4 _ e1 e2 h3
    · refine ⟨fun _ => 0, fun _ => le_rfl, fun S' => ?_, fun v hv => absurd ⟨v, hv⟩ hq⟩
      have h1 := L.thickDensity_pos
      have h2 : 0 < L.sc.b := Real.exp_pos _
      simp only [mul_zero, Finset.sum_const_zero]
      positivity
  choose ρ h0 h1 h2 using key
  rw [← hd.f_eq, ← hd.m_eq, ← hb] at h1
  choose a ha using fun (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Fin D.R.m) => Formalism.MainNotions.Gaps.LocalGlobalPassage.exists_vw_eq v (O.E v i)
  refine ⟨O.Th, a, fun v i => ρ False i v, fun v i => ρ True i v, L.de2, ?_, L.thickDensity_pos.le, L.thickDensity_le_one,
    fun v i => ⟨h0 _ i v, h0 _ i v⟩, fun i S' => ⟨h1 _ i S', h1 _ i S'⟩⟩
  have hloc : ∀ v (i : Fin D.R.m) (W : Submodule D.what₂.LL (Fin (O.nZ i) → D.what₂.LL)),
      (lix v (_root_.Formalism.EigenvalueLevelCeiling.cut W (O.Ms i)) (_root_.Formalism.EigenvalueLevelCeiling.cut W (O.Th v i)) : ℝ) ≤ (O.E v i : ℝ) * (finrank D.what₂.LL W : ℝ) +
        (if Formalism.EigenvalueLevelCeiling.plc v = O.pde then ρ True i v else ρ False i v) := by
    intro v i W
    rw [hO.pde_eq]
    split_ifs with hv
    · exact h2 True i v (iff_true_intro hv) W
    · exact h2 False i v (iff_false_intro hv) W
  intro w hw
  exact ⟨fun i => ⟨((hSp w hw).1 i).1, le_rfl, (ha _ i).1, (ha _ i).2, hloc _ i⟩,
    fun i => ⟨((hSp w hw).2 i).1, le_rfl, (ha _ i).1, (ha _ i).2, hloc _ i⟩⟩

end GlobalTheory.BigOn

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem inf_mu_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ),
    IsMu μ e → ∀ k : Eˣ, ((μ.inf k : ℂˣ) : ℂ) = ∏ v : InfinitePlace E, (v.embedding (k : E) / (‖v.embedding (k : E)‖ : ℂ)) ^ e v := by
  intro E _ _ _ μ e hμ k
  have h1 : μ.inf k = chiInf μ (Units.map (GlobalTheory.CuspRep.pInf E).toMonoidHom (Neutral.B1.diagUnits E k)) := by
    rw [chiInf, MonoidHom.comp_apply, GlobalTheory.CuspRep.NormTriv.infId_pInf]
    change μ.1 (Formalism.L2.Host.infDiag k) = _
    rw [Formalism.L2.Host.infDiag, MonoidHom.finsetProd_apply]
    rfl
  rw [h1, hμ.2.2.2.2]
  refine Finset.prod_congr rfl fun v _ => ?_
  have : (Units.map (GlobalTheory.CuspRep.pInf E).toMonoidHom (Neutral.B1.diagUnits E k)).1 v = v.embedding (k : E) :=
    GlobalTheory.CuspRep.pInf_algebraMap (k : E) v
  rw [this]

end GlobalTheory.BCT
end
