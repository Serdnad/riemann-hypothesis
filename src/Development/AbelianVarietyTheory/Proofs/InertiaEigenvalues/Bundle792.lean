module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle072
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle145
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle439
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle657
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle783
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle654
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle784
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.EigOnto




theorem main : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w), ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) = c v k := by
  intro hstdP D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB j w h1 h2 hw c hc
  classical
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  obtain ⟨-, y, hy, hcy⟩ := hc

  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  have hb := Sp.B.iV_basis j w b
  obtain ⟨a⟩ : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    apply hy
    have hy' : y ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (D.what₂.muTw w) j (b a)) := by
      rw [hjb.2]; exact Submodule.mem_top
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hy'
    exact hy'
  haveI : Nontrivial (Sp.B.V j w) := ⟨⟨Sp.B.iV j w (b a), 0, hb.1.ne_zero a⟩⟩
  obtain ⟨I0, hI0⟩ := Ideal.exists_maximal (heckeAlg Sp.B j w)
  obtain ⟨i0, hi0, -⟩ := Sp.mx_all j w h1 h2 hw I0 hI0

  have hinjC : Function.Injective (Sp.iotaC j w) := by
    intro a1 a2 hab
    obtain ⟨a1', rfl⟩ := (Sp.phO j w i0 hi0).surjective a1
    obtain ⟨a2', rfl⟩ := (Sp.phO j w i0 hi0).surjective a2
    rw [← Sp.iotaC_coh, ← Sp.iotaC_coh] at hab
    congr 1
    exact IsFractionRing.injective _ _ ((Sp.iq i0).injective ((qCast _ _).injective hab))
  let φ : FractionRing (Sp.B.Oc j w) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = Sp.iotaC j w z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (Sp.phK j w i0 hi0).toRingHom =
      (qCast (L.X.nd.w_l i0) (A.pl.ι (L.X.nd.w i0))).toRingHom.comp (Sp.iq i0) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (L.X.nd.O i0))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Sp.phK_alg, hφalg]
    exact (Sp.iotaC_coh j w i0 hi0 z).symm
  have hφ : ∀ x, φ (Sp.B.ec j w x) = D.what₂.embLL x := by
    intro x
    rw [← Sp.phK_emb j w i0 hi0 x, ← Sp.iq_LL i0 x]
    exact congrArg (fun f : FractionRing (L.X.nd.O i0) →+* ℂ => f (L.X.nd.embK i0 x)) hφK

  obtain ⟨Hk, -⟩ := GlobalTheory.FitHecke.heckeOpen_withLoc D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
    big L Sp Au
  obtain ⟨ej, ew⟩ := (L.X.nd.locs_mem j w i0).1 hi0
  have hμ0 : L.X.nd.mu i0 = D.what₂.muTw w := by rw [L.X.nd.mu_w i0, ew]
  have hQk : Hk.cover.B.Qc j w = C.Q w :=
    (Hk.cover.Q_eq j w i0 hi0).symm.trans ((Sp.Q_eq j w i0 hi0).trans (Sp.Qc_eq j w))
  have lin : ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (C.Q w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → (M (D.what₂.muTw w) j h1 h2).wt.W),
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k (z • f + f') =
          z • NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k f + NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k f' := by
    intro v k s ϖ hvk hc hu
    have H := GlobalTheory.LiftPoint.tN_lin (withLoc L) (mtL L M) Hk.hecke Hk.cover (j := j) (w := w) (i := i0) hi0 v k s ϖ
      (by rw [hQk]; exact hvk) hc hu
    exact GlobalTheory.FitHecke.mt_transport M (fun μ jj m => ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → m.wt.W),
        NG.tN m.J s ϖ k (z • f + f') = z • NG.tN m.J s ϖ k f + NG.tN m.J s ϖ k f') hμ0 ej
      (L.X.nd.j_range i0).1 (L.X.nd.j_range i0).2 h1 h2 H

  have hstd : HeckeStdTw Sp.B := heckeStdTw_of_std Sp.std
  have hLoc : LocPl D j w := Or.inl hw
  have hgen : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      GenAt D (D.what₂.places.resChar w) (C.Q w) v k := fun v k h => by rw [← Sp.Qc_eq j w]; exact h
  have key : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      ∃ κ : Sp.B.Oc j w, φ (algebraMap _ _ κ) = c v k := by
    intro v k hvk
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
    obtain ⟨tC, htC1, htC2⟩ := GlobalTheory.LiftPoint.tC_exists D M Sp.B hstd j w (D.what₂.muTw w) rfl h1 h2 hLoc φ hφ v k hvk
    have ht0 : tC y = c v k • y := by
      apply (M (D.what₂.muTw w) j h1 h2).real_inj
      rw [← htC2 s ϖ hc hu (lin v k s ϖ (hgen v k hvk) hc hu) y, hcy v k s ϖ (hgen v k hvk) hc hu, map_smul]
    exact htC1 (c v k) y hy ht0
  let κF : PlE D.host → ℕ → Sp.B.Oc j w := fun v k =>
    if hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k then Classical.choose (key v k hvk) else 0
  have hκF : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), φ (algebraMap _ _ (κF v k)) = c v k := by
    intro v k hvk
    simp only [κF, dif_pos hvk]
    exact Classical.choose_spec (key v k hvk)

  obtain ⟨e, hene, he⟩ := GlobalTheory.PtLocalEig.eig_descends D M Sp.B j w (D.what₂.muTw w) h1 h2 rfl φ hφ
    (fun v k => algebraMap _ _ (κF v k)) y hy (by
      intro v k hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
      refine ⟨s, ϖ, hc, hu, lin v k s ϖ (hgen v k hvk) hc hu, ?_⟩
      rw [hcy v k s ϖ (hgen v k hvk) hc hu, hκF v k hvk])
  have hinjK : Function.Injective (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))) :=
    IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := GlobalTheory.PtLocalEig.pt_of_eigvec (heckeGens Sp.B j w) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨κF v k, he v k hvk⟩)
  have hψv : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      ψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = κF v k := by
    intro v k hvk
    apply hinjK
    have e1 := hψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have e2 := he v k hvk
    change Sp.B.hK j w v k e = _ at e1
    rw [e2] at e1
    exact (smul_left_injective _ hene e1).symm
  have hW : NCov.W (heckeAlg Sp.B j w) (NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3

  obtain ⟨i, hi, hmx⟩ := Sp.mx_all j w h1 h2 hw (NCov.cls ψ) (NCov.cls_isMaximal ψ)
  refine ⟨i, hi, (Sp.ptX j w i hi).symm ⟨ψ, hmx.symm, hW⟩, fun v k hvk => ?_⟩
  have hvk' : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by rw [Sp.Qc_eq j w]; exact hvk
  have e1 : ∀ z, iotaO L.X.nd L.Y.naut i z = Sp.iotaC j w (Sp.phO j w i hi z) := by
    intro z
    unfold iotaO
    rw [RingHom.comp_apply, RingHom.comp_apply, Au.iotaQ i, Au.iotaQC i]
    exact Sp.iotaC_coh j w i hi z
  rw [e1, Sp.ptX_hT j w i hi _ v k hvk', Equiv.apply_symm_apply]
  show Sp.iotaC j w (ψ ⟨Sp.B.hK j w v k, _⟩) = c v k
  rw [hψv v k hvk', ← hφalg, hκF v k hvk']

end GlobalTheory.EigOnto

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.SuppIne

open GlobalTheory.LocGL GlobalTheory.SmGL

section Transport

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem continuous_glMap {n : Type} [Fintype n] [DecidableEq n] (j : k' →+* k) (hj : Continuous j) :
    Continuous (Matrix.GeneralLinearGroup.map (n := n) j) :=
  Units.continuous_iff.2 ⟨continuous_matrix fun a b => hj.comp (Units.continuous_val.matrix_elem a b),
    continuous_matrix fun a b => hj.comp (Units.continuous_coe_inv.matrix_elem a b)⟩

theorem glMap_surjective {n : Type} [Fintype n] [DecidableEq n] (i : k ≃+* k') :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom) := fun g =>
  ⟨Matrix.GeneralLinearGroup.map i.toRingHom g, Units.ext (Matrix.ext fun _ _ => i.symm_apply_apply _)⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] in
theorem isSubquotient_comp {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) (ψ : G' →* G) :
    IsSubquotient (σ.comp ψ) (ρ.comp ψ) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩, ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩

def trGL (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL (k := k)) : IrrGL (k := k') :=
  IrrGL.of (x.rep.comp (Matrix.GeneralLinearGroup.map (n := Fin x.1) i.symm.toRingHom))
    (fun v => (x.2.rep.smooth v).preimage (continuous_glMap _ hi'))
    (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp x.2.rep.irr _ (glMap_surjective i))

theorem hasSupport_comp (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) {N : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL (k := k))}
    (h : HasSupport π s) :
    HasSupport (π.comp (Matrix.GeneralLinearGroup.map (n := Fin N) i.symm.toRingHom)) (s.map (trGL i hi')) := by
  obtain ⟨c, x, rfl, hir, hc, e, hsub⟩ := h
  have H : IsCuspSupport (π.comp (Matrix.GeneralLinearGroup.map (n := Fin N) i.symm.toRingHom)) (fun a => (x a).1)
      (fun a => (x a).rep.comp (Matrix.GeneralLinearGroup.map (n := Fin (x a).1) i.symm.toRingHom)) := by
    refine ⟨GlobalTheory.CuspRep.ParLaws.isIrreducible_comp hir _ (glMap_surjective i), fun a =>
      ⟨(hc a).1, GlobalTheory.CuspRep.ParLaws.isIrreducible_comp (hc a).2.1 _ (glMap_surjective i),
        GlobalTheory.T.isSupercuspidal_comp_generalLinearGroupMapOfFieldEquiv i hi' _ (hc a).2.2⟩, e, ?_⟩
    obtain ⟨φ⟩ := GlobalTheory.T.parabolicInduction_comp_generalLinearGroupMapOfFieldEquiv i hi hi' (GlobalTheory.T.normalizedAbsValueLocalFieldUnit_map_homeomorph i hi hi') e (fun a => (x a).rep)
    exact (isSubquotient_comp hsub _).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have := hasSupport_of_isCuspSupport H
  rw [Multiset.map_map]
  exact this

end Transport

end GlobalTheory.SuppIne

namespace GlobalTheory.SuppIne

open GlobalTheory.LocGL GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem continuous_symm {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) : Continuous (I.i k v).symm := by
  letI := (I.i k v).toRingHom.toAlgebra
  have : ContinuousSMul ℚ_[D.host.g k] ((D.naut.plGw k v).adicCompletion D.host.E) :=
    continuousSMul_of_algebraMap _ _ (I.cont k v)
  let el : ℚ_[D.host.g k] ≃ₗ[ℚ_[D.host.g k]] (D.naut.plGw k v).adicCompletion D.host.E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) (I.i k v).bijective
  refine el.toContinuousLinearEquiv.symm.continuous.congr fun y => (I.i k v).injective ?_
  exact (el.toContinuousLinearEquiv.apply_symm_apply y).trans ((I.i k v).apply_symm_apply y).symm

def tr {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (ρ : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (hs : GlobalTheory.PRep.IsSmooth ρ.ρ) (hi : ρ.ρ.IsIrreducible) : IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) :=
  ⟨ρ, ρ.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom),
    fun x => (hs x).preimage (continuous_glMap _ (continuous_symm I k v)),
    GlobalTheory.CuspRep.ParLaws.isIrreducible_comp hi _ (glMap_surjective _)⟩

theorem iso_pull {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (ρ : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (hs : GlobalTheory.PRep.IsSmooth ρ.ρ) (hi : ρ.ρ.IsIrreducible) : Nonempty (ρ ≅ pull I k v (tr I k v ρ hs hi)) := by
  have hg : ∀ g : GL (Fin n) ℚ_[D.host.g k], Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun a b => (I.i k v).symm_apply_apply _)
  refine ⟨Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ ρ) fun g => LinearMap.ext fun x => ?_)⟩
  change ρ.ρ g x = ρ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g)) x
  rw [hg]

end GlobalTheory.SuppIne

end
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions

namespace GlobalTheory.TypeVec

def rtHom (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : GAf L n →* Module.End ℂ (GAf L n → ℂ) where
  toFun h := Formalism.L2.NG.rt L n h
  map_one' := by
    apply LinearMap.ext; intro f; funext g
    simp [Formalism.L2.NG.rt]
  map_mul' a b := by
    apply LinearMap.ext; intro f; funext g
    simp [Formalism.L2.NG.rt, mul_assoc]

def IsLiftAt {L : Type} [Field L] [NumberField L] [IsCMField L] {g : ℕ} [Fact g.Prime] {n : ℕ} (s : SplitPlace L)
    (j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)) (y : GL (Fin n) ℤ_[g]) (x : GAf L n) : Prop :=
  TrivOutside {s.v} (x : GA L n) ∧ s.loc n x = Matrix.GeneralLinearGroup.map j.toRingHom (GlobalTheory.GLp.inc g n y)

attribute [local instance] GlobalTheory.TypeRec.factG

def KFix (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E)
    (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E))
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A) : Submodule ℂ A :=
  ⨅ (k : Fin 2) (v : D.nd.PlG k) (y : (GlobalTheory.GLp.red (D.host.g k) D.R.r).ker) (x : GAf D.host.E D.R.r)
    (_ : IsLiftAt (s k v) (j k v) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) x), LinearMap.ker (ρA x - LinearMap.id)

end GlobalTheory.TypeVec

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

namespace GlobalTheory.TypeIdent

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.TypeRec.factG

theorem irreducible_natCast_compl {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {g : ℕ}
    (hin : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (hnot : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) :
    Irreducible ((g : ℕ) : 𝒪[w.adicCompletion E]) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hle : ∀ y : 𝒪[w.adicCompletion E], Valued.v (y : w.adicCompletion E) ≤ 1 := fun y =>
    he.le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 y.2)
  have hunit : ∀ y : 𝒪[w.adicCompletion E], IsUnit y ↔ Valued.v (y : w.adicCompletion E) = 1 := fun y => by
    rw [← he.eq_one_iff_eq_one]
    exact (Valuation.integer.integers (valuation (w.adicCompletion E))).isUnit_iff_valuation_eq_one
  have hv : Valued.v ((g : ℕ) : w.adicCompletion E) = w.intValuation ((g : ℕ) : 𝓞 E) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E), ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    congr 1
    exact ((map_natCast (algebraMap E (w.adicCompletion E)) g).symm).trans
      (congrArg (algebraMap E (w.adicCompletion E)) (map_natCast (algebraMap (𝓞 E) E) g).symm)
  have h1 : w.intValuation ((g : ℕ) : 𝓞 E) ≤ WithZero.exp (-1 : ℤ) := by
    simpa using (w.intValuation_le_pow_iff_mem ((g : ℕ) : 𝓞 E) 1).mpr (by rwa [pow_one])
  have h2 : WithZero.exp (-2 : ℤ) < w.intValuation ((g : ℕ) : 𝓞 E) := by
    by_contra hc
    exact hnot ((w.intValuation_le_pow_iff_mem _ 2).mp (by simpa using not_lt.1 hc))
  have hc : (((g : ℕ) : 𝒪[w.adicCompletion E]) : w.adicCompletion E) = (g : w.adicCompletion E) := by simp
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [hunit, hc, hv]
    intro e
    rw [e, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · have h3 : Valued.v (a : w.adicCompletion E) * Valued.v (b : w.adicCompletion E) =
        w.intValuation ((g : ℕ) : 𝓞 E) := by
      rw [← hv, ← map_mul, ← hc, hab]; rfl
    rw [← h3] at h1 h2
    have h0 := (zero_le.trans_lt h2).ne'
    have ha := left_ne_zero_of_mul h0
    have hb := right_ne_zero_of_mul h0
    have ha1 := hle a
    have hb1 := hle b
    rw [hunit, hunit]
    rw [← WithZero.exp_log ha] at h2 ha1 ⊢
    rw [← WithZero.exp_log hb] at h2 hb1 ⊢
    rw [← WithZero.exp_add, WithZero.exp_lt_exp] at h2
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
    rw [← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
    omega

theorem nonempty_ident : ∀ D : D7, Nonempty (GlobalTheory.TypeRec.Ident D) := by
  intro D
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have key : ∀ k v, ∃ φ : ℚ_[D.host.g k] ≃+* (D.naut.plGw k v).adicCompletion D.host.E, Continuous φ := by
    intro k v
    obtain ⟨h1, h2, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v)
    haveI : CharZero ((D.naut.plGw k v).adicCompletion D.host.E) :=
      charZero_of_injective_ringHom (algebraMap D.host.E _).injective
    obtain ⟨φ, h, -⟩ := GlobalTheory.QpChar.exists_ringEquiv_padic ((D.naut.plGw k v).adicCompletion D.host.E) (D.host.g k)
      ((GlobalTheory.LocLanglands.resCard_eq_normV _).trans (by
        simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h1)) (irreducible_natCast_compl _ (D.naut.plGw_over k v) h2)
    exact ⟨φ, h⟩
  exact ⟨⟨fun k v => (key k v).choose, fun k v => (key k v).choose_spec⟩⟩

end GlobalTheory.TypeIdent

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

theorem GlobalTheory.BKGal.sub_sub_xi_mem_Man : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ σ : D.MMl, D.conn σ.1 = D.zeta y → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), σ.1 - y - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ ι _ _ η H D y hyY hMon σ hσ m
  have hyM : E K l e ^ η • y ∈ D.M := mem_divE.1 hyY.1
  have hσM : E K l e ^ η • σ.1 ∈ D.Mext (invL l (S O K e)) :=
    D.smul_mem_Mext (le_trans (A_le_S l e) (le_away _ _)) σ.2
  have hv : σ.1 - y ∈ divE l e η D.Man := by
    rw [mem_divE, smul_sub]
    exact sub_mem (D.Mext_mono (invL_S_le_Rpi l e) hσM) (D.M_le_Man hyM)
  have hEN : D.EN (σ.1 - y) ∈ D.Man := by
    have h0 : D.EN y - E K l e • D.zeta y ∈ D.Man := by
      rw [← D.cls_eq_zero_iff, ← D.Mon_apply]; exact hMon
    have h1 : D.EN (σ.1 - y) = -(D.EN y - E K l e • D.zeta y) := by
      rw [map_sub, D.EN_apply σ.1, hσ]; abel
    rw [h1]; exact neg_mem h0
  exact GlobalTheory.T.horizontal_mod_breuilKisin_of_eulerNoPole O K l e a ι η H D η _ hv hEN m

theorem GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ (hy : y ∈ ME D.toPhiMod) (σ : D.MMl), σ.1 ∈ D.desc.inv → D.conn σ.1 = D.zeta y → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) - (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hMon hy σ hσinv hconn b₂ hb₂ g hg C
  haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  obtain ⟨m₀, hxi⟩ := GlobalTheory.T.xi_value_galois_sub_mem_filZero l a e O K t ϖ hl2 ι η H D T R
  obtain ⟨w, hw, hr, hN⟩ := GlobalTheory.BKGal.sub_sub_xi_mem_Man l a e O K ι η H D y hyY hMon σ hconn m₀
  have hwM : D.xiExt w ∈ D.MMl :=
    ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι D.toPhiMod).2 w).2 (D.Mext_mono (away_mono (A_le_S l e) rfl) hw)
  set ξw : D.MMl := ⟨D.xiExt w, hwM⟩ with hξw
  have hr' : (σ - ξw).1 - y ∈ D.Man := by
    have : (σ - ξw).1 - y = σ.1 - y - D.xiExt w := by
      rw [Submodule.coe_sub, hξw]; abel
    rw [this]; exact hr
  have h3 := GlobalTheory.T.breuilKisin_hat_value_mem_filZero l a e O K t ϖ hl2 ι η H D T R (σ - ξw) y hy hr' b₂ hb₂ C
  have h4 := GlobalTheory.T.bcrisTensorLattice_filZero_galois_stable l O K T g C _ h3
  have h2 := hxi w hw hN hwM g hg C
  have key : R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ = R.jB (toBcris t ϖ D.toPhiMod ξw) +
      (R.jB (toBcris t ϖ D.toPhiMod (σ - ξw)) - b₂) := by
    rw [map_sub, map_sub]; abel
  rw [key, map_add (f := _)]
  convert add_mem h2 (sub_mem h4 h3) using 1
  abel

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.equivariant_phiModule_matrix_mem_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (X : Matrix (Fin d') (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) → bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) → ∀ i j, X i j ∈ bk.OE := by
  first | exact @GlobalTheory.BSP.EquivOE.main | exact GlobalTheory.BSP.EquivOE.main | (intros; apply GlobalTheory.BSP.EquivOE.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.isUnit_saturated_basis_etale_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), (Y1.map (inclW l)).det ≠ 0 → δ ≠ 0 → bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev → (∀ g : ↥(GK K), bk.FixFlat g → τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • Y1) → ∀ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) → P.det ≠ 0 → (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) → (∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i) → IsUnit Y' := by
  first | exact @GlobalTheory.EtaleLattice.isUnit_saturated_basis | exact GlobalTheory.EtaleLattice.isUnit_saturated_basis | (intros; apply GlobalTheory.EtaleLattice.isUnit_saturated_basis <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.dvd_l_of_galoisSections_breuilKisinCoproduct : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  first | exact @GlobalTheory.BSP.dvd_l_of_sections_env_bk | exact GlobalTheory.BSP.dvd_l_of_sections_env_bk | (intros; apply GlobalTheory.BSP.dvd_l_of_sections_env_bk <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.eisensteinApproxRoot_galois_sub_mem_bdRFil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n M : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X →
    bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) →
    ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev q) - bk.ev q) ∈ Per.FilP l n := by
  first | (exact @GlobalTheory.BSP.approxRoot_gal_sub_mem_fil) | (exact GlobalTheory.BSP.approxRoot_gal_sub_mem_fil) | (intros; apply GlobalTheory.BSP.approxRoot_gal_sub_mem_fil  <;> assumption)
end
