module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle217
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle224
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle212
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle106
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle159
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle289
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FockTranslate

theorem compAt_fin {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) {V : HSp D} (g : GA D V) (hg : g ∈ Formalism.L2.Theta.GfC V) :
    Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h6 : (Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D) = 1 :=
    congrArg Units.val (show Formalism.L2.Theta.infHom V g = 1 from hg)
  unfold Formalism.IndefR.Datum.compAt
  rw [show (Formalism.L2.Theta.mt V g).map (fun a => θ τ (Formalism.L2.Theta.infPart D a)) =
    ((Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D)).map (θ τ) from (Matrix.map_map).symm, h6]
  exact Matrix.map_one _ (θ τ).map_zero (θ τ).map_one

theorem fockComp_translate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : VertexFrames G) (t : T) (j : ℕ),
    j + 1 ≤ D.R.m → ∀ (f : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
    IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) f →
    ∀ (a k₁ : FinPt G (.top j)) (b k₂ : FinPt G (.top (j + 1))),
      fockComp W B (.top t j) f (a * k₁) (b * k₂) =
        fockComp W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) a b := by
  intro D T L sc G W B t j hj f hf a k₁ b k₂
  have hom := W.om_is (.top t j) hj
  have hcomm : ∀ P, W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1)))))
      (fockIn W B (.top t j) f P) = fockIn W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) P := by
    intro P
    unfold fockIn
    refine Formalism.IndefR.Eqv.KerDiag.comm_pureTensorO W.ψ_std W.θ W.θ_is _ _ _ _ _ (fun τ z g hg => ?_) hf P
    rw [GlobalTheory.OrientedHeis.om_dRho hom W.θ_is _ _ τ z hg, compAt_fin W.θ τ _ k₂.2, compAt_fin W.θ τ _ (inv_mem k₁.2),
      Matrix.one_mul, Matrix.mul_one]
  unfold fockComp
  congr 1
  funext M
  unfold jetTab kerFin GridData.Weil.ker
  simp only [GridData.toPair, thetaKO, Subgroup.coe_mul]
  rw [show ((a : GA D (G.V (.top j))) * k₁, (b : GA D (G.V (.top (j + 1)))) * k₂) =
    ((a : GA D (G.V (.top j))), (b : GA D (G.V (.top (j + 1))))) * ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) from rfl,
    map_mul, Module.End.mul_apply, hcomm]

end GlobalTheory.FockTranslate

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZPartEig

theorem heckePolyOf_coeff {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) {k : ℕ} (hk : k ≤ n) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff k = (-1) ^ k * (q : L) ^ (k * (k - 1) / 2) * a k := by
  classical
  simp only [Formalism.L2.Col.heckePolyOf, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hk))]

theorem heckePolyOf_val_eq {L : Type} [Field L] [CharZero L] (n q : ℕ) (hq : q ≠ 0) (a b : ℕ → L)
    (h : Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b) {k : ℕ} (hk : k ≤ n) : a k = b k := by
  have e := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) h
  simp only [heckePolyOf_coeff n q _ hk] at e
  have hne : ((-1 : L) ^ k * (q : L) ^ (k * (k - 1) / 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))
  exact mul_left_cancel₀ hne e

theorem apply_of_mem_maxGen {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : K →+* ℂ) (j : V →ₛₗ[σ] H) (T : Module.End K V)
    (N : Module.End ℂ H) (hN : Commute N (LinearMap.adjoint N)) (hj : ∀ f, j (T f) = N (j f)) (c : K) (f : V)
    (hf : f ∈ T.maxGenEigenspace c) : N (j f) = σ c • j f := by
  have key : ∀ (k : ℕ) (g : V), j (((T - c • (1 : Module.End K V)) ^ k : Module.End K V) g) =
      (((N - σ c • (1 : Module.End ℂ H)) ^ k : Module.End ℂ H) (j g)) := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp [hj, map_smulₛₗ]
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf
  have h0 : (((N - σ c • (1 : Module.End ℂ H)) ^ k : Module.End ℂ H) (j f)) = 0 := by rw [← key, hk, map_zero]
  have hmem : j f ∈ N.maxGenEigenspace (σ c) := (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, h0⟩
  rw [GlobalTheory.NormalFamily.maxGenEigenspace_eq hN] at hmem
  exact Module.End.mem_eigenspace_iff.1 hmem

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

open GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def OpLab (R : RealDat3 D A3 Ks) (i : Fin D.R.m) : (A3.liftI i A3.A.μ0).OpIx → Pl D.host.E → List ℤ → Prop :=
  Sum.elim
    (fun k P d => R.pl ((A3.A.fam.L i A3.A.μ0).pl k.1) = P ∧ k.2 ≤ (Vc D i).rank ∧ d = splitLab (Vc D i).rank k.2)
    (fun k P d => R.plI ((A3.liftI i A3.A.μ0).plI k.1) = P ∧ Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2 ∧
      d = GlobalTheory.Hk3.labIn (Vc D i).rank k.2)

theorem opLab_ops (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i A3.A.μ0).H) (hh : GlobalTheory.Hk3.IsOpsV R.toRealDat i A3.A.μ0 h) :
    ∀ idx P d, OpLab R i idx P d → GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧
      ∀ f, R.jV i A3.A.μ0 ((A3.liftI i A3.A.μ0).opAll idx f) = h P (Finsupp.single d 1) (R.jV i A3.A.μ0 f) := by
  have hlev := hC.base.lev
  have hfam := hC.base.fam
  have hmod := hC.base.models
  have c3 := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC).2.2.1
  rintro (⟨⟨P', hP'⟩, k⟩ | ⟨⟨Q, hQ⟩, s'⟩) P d hc
  · obtain ⟨rfl, hk, rfl⟩ := hc
    refine ⟨((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hlev).2.2.2 hfam A3.A.μ0 P' hP').1, fun f => ?_⟩
    exact (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hlev hfam hmod).2 i A3.A.μ0 h hh ⟨P', hP'⟩ k hk f
  · obtain ⟨rfl, hs, rfl⟩ := hc
    have hty : ∀ k : A3.okI A3.A.μ0 × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2 →
        GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 (R.plI k.1) ∧ Formalism.DivisionValues.conjPl (R.plI k.1) = R.plI k.1 ∧
          (GlobalTheory.Hk3.labIn (Vc D i).rank k.2).Pairwise (fun a b => b ≤ a) := fun k hk =>
      ⟨(c3 A3.A.μ0 k.1 k.1.2).1, (c3 A3.A.μ0 k.1 k.1.2).2,
        ((GlobalTheory.Hk3.labIn_selfDual_iff (Vc D i).rank _).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1⟩
    refine ⟨(c3 A3.A.μ0 Q hQ).1, fun f => ?_⟩
    exact (GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hlev hfam hmod i A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
      (fun k => R.plI k.1) (fun k => GlobalTheory.Hk3.labIn (Vc D i).rank k.2) (A3.heckeLI i A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2) hty (hC.inert.hL i A3.A.μ0).some (⟨Q, hQ⟩, s') hs).2.2.2 h hh f

theorem exists_opLab (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m) :
    ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → RelLab (Vc D i) P d → ∃ idx, OpLab R i idx P d := by
  have c3 := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC).2.2.2.1
  intro P d hg hr
  rcases hr with ⟨hc, k, hk, rfl⟩ | ⟨hc, hl⟩
  · obtain ⟨P0, hP0, rfl⟩ := (c3 P hg).2 hc
    exact ⟨Sum.inl (⟨P0, hP0⟩, k), rfl, hk, rfl⟩
  · obtain ⟨Q, hQ, rfl⟩ := (c3 P hg).1 hc
    obtain ⟨hlen, hpw, hdual⟩ := (GlobalTheory.LabChar.labels_char (Vc D i) _ d).1 hl
    obtain ⟨s', h1, h2, h3, rfl⟩ := (GlobalTheory.Hk3.labIn_selfDual_iff (Vc D i).rank d).1 ⟨hlen, hpw, hdual hc⟩
    exact ⟨Sum.inr (⟨Q, hQ⟩, s'), rfl, ⟨h2, h3, h1⟩, rfl⟩

theorem opLab_val_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ)) :
    ∀ idx P d, OpLab R i idx P d → ∀ y y', (A3.liftI i A3.A.μ0).HasRes3 q y → (A3.liftI i A3.A.μ0).HasRes3 q y' →
      y idx = y' idx := by
  rintro (⟨⟨P', hP'⟩, k⟩ | ⟨Q, s'⟩) P d hc y y' hy hy'
  · obtain ⟨-, hk, -⟩ := hc
    have hq : (A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩ ≠ 0 := by
      show A3.A.q P' ≠ 0
      rw [((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.base.lev).2.2.2 hC.base.fam A3.A.μ0 P' hP').2.2]
      exact fun h0 => (R.pl P').ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have e : Formalism.L2.Col.heckePolyOf (A3.A.fam.L i A3.A.μ0).n ((A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩)
          (fun j => y (Sum.inl (⟨P', hP'⟩, j))) =
        Formalism.L2.Col.heckePolyOf (A3.A.fam.L i A3.A.μ0).n ((A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩)
          (fun j => y' (Sum.inl (⟨P', hP'⟩, j))) :=
      (hy.1 ⟨P', hP'⟩).trans (hy'.1 ⟨P', hP'⟩).symm
    have hk' : k ≤ (A3.A.fam.L i A3.A.μ0).n := by
      have e2 : (A3.A.fam.L i A3.A.μ0).n = A3.A.r + A3.A.t := rfl
      rw [e2, ← R.B.rankL i]; exact hk
    exact heckePolyOf_val_eq _ _ hq _ _ e hk'
  · exact (hy.2 (Q, s')).trans (hy'.2 (Q, s')).symm

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem thetaLiftPoint_mem_jointEigenspace_of_part (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : (R.toCx3 F).H3W F.cr false) (i : Fin D.R.m)
    (p : A3.fam3.base3.Ix) (x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL)
    (hx : (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p) :
    F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x ∈ (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum (A3.fam3.tr3 i p.1) := by
  have hZ := (hW i p x).2 hx
  have h2 : (A3.A.fam.L i A3.A.μ0).vE (A3.A.fam.lvlA F.P0 F.ψ0) *ᵥ
      ((A3.A.fam.L i A3.A.μ0).zE (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).zs.Zl i A3.A.μ0) *ᵥ x) ∈
      ((A3.liftI i A3.A.μ0).inertTypeEigenspaceSum (A3.fam3.tr3 i p.1)).map
        ((A3.A.fam.L i A3.A.μ0).S.basis.equivFun : (A3.A.fam.L i A3.A.μ0).S.Forms →ₗ[D.what₂.LL] _) := hZ
  obtain ⟨g, hg, hge⟩ := Submodule.mem_map.1 h2
  convert hg using 1
  rw [← LinearEquiv.symm_apply_apply (A3.A.fam.L i A3.A.μ0).S.basis.equivFun g]
  erw [hge]
  rfl

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

open GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def eigVal (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ)) (P : Pl D.host.E) (d : List ℤ) :
    D.what₂.LL :=
  if hx : (∃ y, (A3.liftI i A3.A.μ0).HasRes3 q y) ∧ ∃ idx, OpLab R i idx P d then hx.1.choose hx.2.choose else 0

theorem eig_of_mem (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ))
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i A3.A.μ0).H) (hh : GlobalTheory.Hk3.IsOpsV R.toRealDat i A3.A.μ0 h)
    (hn : GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0) h) (f : (A3.A.fam.L i A3.A.μ0).S.Forms)
    (hf : f ∈ (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum q) :
    ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → RelLab (Vc D i) P d →
      h P (Finsupp.single d 1) (R.jV i A3.A.μ0 f) = D.what₂.embLL (eigVal R i q P d) • R.jV i A3.A.μ0 f := by
  let E : Submodule ℂ (R.HV i A3.A.μ0).H :=
    ⨅ (P : Pl D.host.E) (d : List ℤ) (_ : GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧ RelLab (Vc D i) P d),
      (h P (Finsupp.single d 1)).eigenspace (D.what₂.embLL (eigVal R i q P d))
  have hle : (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum q ≤ E.comap (R.jV i A3.A.μ0) := by
    unfold InertDat3.inertTypeEigenspaceSum Formalism.L2.Col.eigSum
    refine iSup₂_le fun y hy g hg => ?_
    rw [Submodule.mem_comap]
    simp only [E, Submodule.mem_iInf]
    rintro P d ⟨hgd, hr⟩
    have hex : (∃ y, (A3.liftI i A3.A.μ0).HasRes3 q y) ∧ ∃ idx, OpLab R i idx P d :=
      ⟨⟨y, hy⟩, exists_opLab R F hC i P d hgd hr⟩
    have ha : eigVal R i q P d = hex.1.choose hex.2.choose := by
      unfold eigVal
      rw [dite_eq_left hex]
    have ha' : eigVal R i q P d = y hex.2.choose :=
      ha.trans (opLab_val_eq R F hC i q _ P d hex.2.choose_spec _ _ hex.1.choose_spec hy)
    have hop := opLab_ops R F hC i h hh _ P d hex.2.choose_spec
    have hN : Commute (h P (Finsupp.single d 1)) (LinearMap.adjoint (h P (Finsupp.single d 1))) :=
      (congrArg (Commute (h P (Finsupp.single d 1))) (hn.2 P hop.1 (Finsupp.single d 1))).mpr (hn.1 P P hop.1 hop.1 _ _)
    have key := apply_of_mem_maxGen D.what₂.embLL (R.jV i A3.A.μ0) ((A3.liftI i A3.A.μ0).opAll hex.2.choose) _ hN hop.2
      (y hex.2.choose) g (Formalism.L2.Col.eigAt_le (A3.liftI i A3.A.μ0).opAll y hex.2.choose hg)
    exact Module.End.mem_eigenspace_iff.2 (key.trans (congrArg (fun c => D.what₂.embLL c • R.jV i A3.A.μ0 g) ha'.symm))
  intro P d hg hr
  have e1 := hle hf
  rw [Submodule.mem_comap] at e1
  simp only [E, Submodule.mem_iInf] at e1
  exact Module.End.mem_eigenspace_iff.1 (e1 P d ⟨hg, hr⟩)

theorem points_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → (R.toCx3 F).H3W F.cr false → ∀ i p, ∃ a, ∀ x, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p → GlobalTheory.ConjScalar.EigK R.toRealDat i a (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s _hOk hC hW i p
  obtain ⟨h, hh, hn⟩ :=
    (GlobalTheory.DefiniteOps.definite_ops R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models).2 i A3.A.μ0
  refine ⟨eigVal R i (A3.fam3.tr3 i p.1), fun x hx => ?_⟩
  have hm := thetaLiftPoint_mem_jointEigenspace_of_part R F hW i p x hx
  intro P d hg hr
  have e1 := eig_of_mem R F hC i _ h hh hn _ hm P d hg hr
  have e2 := hh P hg (Finsupp.single d 1) (R.jV i A3.A.μ0 (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x))
  exact e2.symm.trans ((congrArg (R.HV i A3.A.μ0).e e1).trans (map_smul _ _ _))

end GlobalTheory.ZPartEig
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace
open scoped ENNReal

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ} {N : ℕ}

private lemma rderC_sum_smul (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (M : ι → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ (∑ a ∈ s, c a • M a) φ = ∑ a ∈ s, c a • RderC θ V τ (M a) φ := by
  induction s using Finset.induction_on with
  | empty =>

    have h0 := GlobalTheory.Mem.RealTranslate.RderC_smul hθ hs τ (0 : ℂ) (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    rw [zero_smul, zero_smul] at h0
    rw [Finset.sum_empty, Finset.sum_empty, h0]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, GlobalTheory.Mem.RealTranslate.RderC_add hθ hs,
      GlobalTheory.Mem.RealTranslate.RderC_smul hθ hs, ih]

theorem RderC_eq_sum_glDer (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z φ = ∑ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • glDer θ V (τ, a) φ := by

  have hZ : Z = ∑ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • Matrix.single a.1 a.2 (1 : ℂ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Fintype.sum_prod_type]

    rw [Fintype.sum_eq_single i fun x hx => by simp [hx], Fintype.sum_eq_single j fun y hy => by simp [hy]]
    simp
  conv_lhs => rw [hZ]
  rw [rderC_sum_smul hθ hs τ]
  simp only [glDer]

theorem Rder_eq_sum_glDer (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X φ = ∑ a : Fin V.rank × Fin V.rank, X a.1 a.2 • glDer θ V (τ, a) φ := by

  rw [← GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX φ]
  exact RderC_eq_sum_glDer hθ hs τ X


variable (θ V N) in
def wordFin (l : List (D.what₂.Tau × Fin V.rank × Fin V.rank)) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | f ∈ SmFun θ V ∧ growthSize V N (wordAct (glDer θ V) l f) ≠ ∞}
  add_mem' h h' := ⟨add_mem h.1 h'.1, by
    rw [(linOnSm_glWord l).add _ h.1 _ h'.1]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h.2, h'.2⟩) growthSize_add_le⟩
  zero_mem' := ⟨zero_mem _, by
    have := (linOnSm_glWord (θ := θ) l).smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    exact (growthSize_const (0 : ℂ)).trans_ne enorm_ne_top⟩
  smul_mem' c _ h := ⟨(SmFun θ V).smul_mem c h.1, by
    rw [(linOnSm_glWord l).smul, growthSize_smul]
    exact ENNReal.mul_ne_top enorm_ne_top h.2⟩

theorem rWord_mem_wordFin (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {d : ℕ} (h : growthSob θ V d N φ ≠ ∞)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : IsLieWord V l) :
    ∀ l', l'.length + l.length ≤ d → rWord θ V l φ ∈ wordFin θ V N l' := by
  have hsum : wordSum (glDer θ V) (growthSize V N) d φ ≠ ∞ := h
  induction l with
  | nil =>

    intro l' hl'
    have hlen : l'.length ≤ d := by simpa using hl'
    have hw : rWord θ V [] φ = φ := wordAct_nil _ φ
    rw [hw]
    show φ ∈ SmFun θ V ∧ growthSize V N (wordAct (glDer θ V) l' φ) ≠ ∞
    exact ⟨hs, wordSum_ne_top_iff.1 hsum l' hlen⟩
  | cons p t ih =>

    intro l' hl'
    have hp : p.2 ∈ lieAt V p.1 := hl p (List.mem_cons_self ..)
    have ht : IsLieWord V t := fun q hq => hl q (List.mem_cons_of_mem p hq)
    have hψ : rWord θ V t φ ∈ SmFun θ V :=
      (show _ ∧ _ from ih ht [] (by simp only [List.length_cons, List.length_nil] at hl' ⊢; omega)).1
    have hw : rWord θ V (p :: t) φ = Rder θ V p.1 p.2 (rWord θ V t φ) := wordAct_cons _ p t φ
    rw [hw, Rder_eq_sum_glDer hθ hψ hp]
    refine sum_mem fun a _ => Submodule.smul_mem _ _ ?_
    have hm : growthSize V N (wordAct (glDer θ V) (l' ++ [(p.1, a)]) (rWord θ V t φ)) ≠ ∞ :=
      (show _ ∧ _ from ih ht (l' ++ [(p.1, a)])
        (by simp only [List.length_cons, List.length_append, List.length_nil] at hl' ⊢; omega)).2
    have he : wordAct (glDer θ V) (l' ++ [(p.1, a)]) (rWord θ V t φ) =
        wordAct (glDer θ V) l' (glDer θ V (p.1, a) (rWord θ V t φ)) := by
      rw [wordAct_append, wordAct_cons, wordAct_nil]
    show glDer θ V (p.1, a) (rWord θ V t φ) ∈ SmFun θ V ∧
      growthSize V N (wordAct (glDer θ V) l' (glDer θ V (p.1, a) (rWord θ V t φ))) ≠ ∞
    rw [← he]
    exact ⟨(linOnSm_RderC p.1 _).mem _ hψ, hm⟩

theorem growthSize_rWord_ne_top_of_le (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {d : ℕ} (h : growthSob θ V d N φ ≠ ∞)
    {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) (hd : l.length ≤ d) :
    growthSize V N (rWord θ V l φ) ≠ ∞ := by
  have hm := rWord_mem_wordFin hθ hs h l hl [] (by simpa using hd)
  have h2 : growthSize V N (wordAct (glDer θ V) [] (rWord θ V l φ)) ≠ ∞ := (show _ ∧ _ from hm).2
  rwa [wordAct_nil] at h2

theorem growthSize_rWord_ne_top (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (h : ∀ d, growthSob θ V d N φ ≠ ∞) :
    ∀ l, IsLieWord V l → growthSize V N (rWord θ V l φ) ≠ ∞ := fun l hl =>
  growthSize_rWord_ne_top_of_le hθ hs (h l.length) hl le_rfl

theorem unifModGrowth_iff_growthSob (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) :
    UnifModGrowth V θ φ ↔ ∃ N, ∀ d, growthSob θ V d N φ ≠ ∞ := by
  refine ⟨exists_growthSob_ne_top hs, ?_⟩
  rintro ⟨M, hM⟩
  exact unifModGrowth_iff.2 ⟨M, growthSize_rWord_ne_top hθ hs hM⟩

end GlobalTheory.Size

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLimit

theorem integral_eq_zero_of_approx {X : Type} [MeasurableSpace X] {μ : Measure X} {u : ℕ → X → ℂ} {v : X → ℂ}
    {w : X → ℝ} (hu : ∀ n, Integrable (u n) μ) (hv : Integrable v μ) (hw : Integrable w μ)
    (h0 : ∀ n, ∫ x, u n x ∂μ = 0) (h : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x, ‖u n x - v x‖ ≤ ε * w x) :
    ∫ x, v x ∂μ = 0 := by
  have key : ∀ ε : ℝ, 0 < ε → ‖∫ x, v x ∂μ‖ ≤ ε * ∫ x, w x ∂μ := fun ε hε => by
    obtain ⟨n, hn⟩ := h ε hε
    have e : ∫ x, (u n x - v x) ∂μ = -∫ x, v x ∂μ := by rw [integral_sub (hu n) hv, h0, zero_sub]
    rw [← norm_neg, ← e, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall hn)
  have t : Filter.Tendsto (fun ε : ℝ => ε * ∫ x, w x ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * ∫ x, w x ∂μ)) :=
    ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul] at t
  exact norm_le_zero_iff.1 (ge_of_tendsto t (eventually_nhdsWithin_of_forall key))

theorem isCuspFun_of_tendsto : ∀ (D : D7) (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ) (f : GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ (∀ γ ∈ GQ V, ∀ g, ψ n (γ * g) = ψ n g) ∧ IsCuspFun V (ψ n)) → Continuous f → (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → Filter.Tendsto (fun n => GlobalTheory.Size.growthSize V N (ψ n - f)) Filter.atTop (nhds 0) → IsCuspFun V f := by
  intro D V N ψ f hψ hf hl ht
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
      ∀ W, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W → ∀ μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRat D.sp.cm V W) 𝓕 μ → ∀ g : GA D V,
        IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl W hW μ hμ 𝓕 h𝓕 g
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.Size.quotHeight_laws V
  have hw := (hint (fun x => ((GlobalTheory.Grow.quotHeight V x ^ N : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (h4.pow N)) (fun γ hγ x => by rw [h2 γ hγ]) W hW μ hμ 𝓕 h𝓕 g).re
  refine integral_eq_zero_of_approx (μ := μ.restrict 𝓕) (u := fun k n => ψ k (n.1 * g)) (v := fun n => f (n.1 * g))
    (fun k => hint _ (hψ k).1 (hψ k).2.1 W hW μ hμ 𝓕 h𝓕 g) (hint _ hf hl W hW μ hμ 𝓕 h𝓕 g) hw
    (fun k => (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V _).1 (hψ k).2.2 W hW μ hμ 𝓕 h𝓕 g) fun ε hε => ?_
  obtain ⟨k, hk⟩ := (ht.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  refine ⟨k, fun n => ?_⟩
  rw [GlobalTheory.Size.growthSize_eq_quot (fun γ hγ x => by
    rw [Pi.sub_apply, Pi.sub_apply, (hψ k).2.1 γ hγ, hl γ hγ])] at hk
  have := (ENNReal.ofReal_le_ofReal_iff hε.le).1 ((le_iSup _ (n.1 * g)).trans hk)
  exact (div_le_iff₀ (pow_pos (lt_of_lt_of_le one_pos (h1 _).1) N)).1 this

end GlobalTheory.CuspLimit
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mixedModelTerm_derivative_isotropicDirection : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y = (2 * Real.pi * Complex.I * ((2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTerm.IsoDeriv.term_dRho_dirAt | exact GlobalTheory.MixedTerm.IsoDeriv.term_dRho_dirAt | (intros; apply GlobalTheory.MixedTerm.IsoDeriv.term_dRho_dirAt <;> assumption)
end
