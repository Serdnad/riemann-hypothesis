module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle319
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle758
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle735
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle803
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle791
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle145
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle707
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle659
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle782
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle804
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle663
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle653
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle683
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle661
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle536
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.PtExt



theorem main : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), Built A M C tp.tup big₀ L₀ → Built A M C tp.tup big₁ L₁ → ∀ i₁ : L₁.lay.fixZ.nd.Loc, ∃ i₀ : L₀.lay.fixZ.nd.Loc, L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ ∧ L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ ∧ ∃ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, ∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x)) := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big₀ big₁ L₀ L₁ hB₀ hB₁ i₁
  have onto : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 →
      ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w),
        ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, sys L i x = c := by
    intro big L hB j w h1 h2 htw c hc
    obtain ⟨i, hi, x, hx⟩ := GlobalTheory.T.side_eigen_frobenius hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big L hB j w h1 h2 htw c hc
    refine ⟨i, hi, x, funext fun v => funext fun k => ?_⟩
    by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
    · rw [sys_of_genAt hB hi x hg, hx v k hg]
    · rw [sys_of_not_genAt hB hi x hg, hc.1 v k hg]
  have cong : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w →
      ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'),
        (i = i' ↔ ∀ v k, sys L i x v k - sys L i' x' v k ∈ (A.pl.plB w).nonunits) := by
    intro big L hB j w i i' hi hi' x x'
    rw [GlobalTheory.T.locations_distinguished_by_generics D cf jE A M C tp.tup big L hB j w i i' hi hi' x x']
    constructor
    · intro h v k
      by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
      · rw [sys_of_genAt hB hi x hg, sys_of_genAt hB hi' x' hg]; exact h v k hg
      · rw [sys_of_not_genAt hB hi x hg, sys_of_not_genAt hB hi' x' hg, sub_zero]; exact zero_mem _
    · intro h v k hg
      rw [← sys_of_genAt hB hi x hg, ← sys_of_genAt hB hi' x' hg]; exact h v k
  have h1 := (L₁.X.nd.j_range i₁).1
  have h2 := (L₁.X.nd.j_range i₁).2
  have hi₁ : i₁ ∈ L₁.X.nd.locs (L₁.X.nd.j i₁) (L₁.X.nd.w i₁) := (L₁.X.nd.locs_mem _ _ i₁).2 ⟨rfl, rfl⟩
  have htw : D.what₂.muAt (L₁.X.nd.w i₁) ≠ D.what₂.mu0 := L₁.X.nd.w_tw i₁
  obtain ⟨x₁⟩ := L₁.X.nd.neX i₁
  obtain ⟨i₀, hi₀, y₀, hy₀⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (sys_mem hB₁ h1 h2 hi₁ x₁)
  have fwd : ∀ x : L₁.X.nd.X i₁, ∃ y : L₀.X.nd.X i₀, sys L₀ i₀ y = sys L₁ i₁ x := by
    intro x
    obtain ⟨i', hi', y', hy'⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (sys_mem hB₁ h1 h2 hi₁ x)
    have hc : i' = i₀ := by
      rw [cong big₀ L₀ hB₀ _ _ i' i₀ hi' hi₀ y' y₀, hy', hy₀]
      exact (cong big₁ L₁ hB₁ _ _ i₁ i₁ hi₁ hi₁ x x₁).1 rfl
    subst hc
    exact ⟨y', hy'⟩
  choose f hf using fwd
  have finj : Function.Injective f := fun x x' h => sys_inj L₁ i₁ (by rw [← hf x, ← hf x', h])
  have fsurj : Function.Surjective f := by
    intro y
    obtain ⟨i', hi', x', hx'⟩ := onto big₁ L₁ hB₁ _ _ h1 h2 htw _ (sys_mem hB₀ h1 h2 hi₀ y)
    have hc : i' = i₁ := by
      rw [cong big₁ L₁ hB₁ _ _ i' i₁ hi' hi₁ x' x₁, hx', ← hy₀]
      exact (cong big₀ L₀ hB₀ _ _ i₀ i₀ hi₀ hi₀ y y₀).1 rfl
    subst hc
    exact ⟨x', sys_inj L₀ i₀ (by rw [hf x', hx'])⟩
  have hw₀ : L₀.X.nd.w i₀ = L₁.X.nd.w i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).2
  have hj₀ : L₀.X.nd.j i₀ = L₁.X.nd.j i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).1
  refine ⟨i₀, hw₀, hj₀, Equiv.ofBijective f ⟨finj, fsurj⟩, fun v k x hv k1 k2 => ?_⟩
  have hg := (splitOut_iff_genAt hB₁ hi₁ v k).1 ⟨hv, k1, k2⟩
  have e := congrFun (congrFun (hf x) v) k
  rw [sys_of_genAt hB₀ hi₀ _ hg] at e
  exact (sys_of_genAt hB₁ hi₁ x hg).symm.trans e.symm

end GlobalTheory.PtExt

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LiftOther

theorem proj_eq_comp {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L) :
    s.proj z = (Algebra.TensorProduct.lift s.i (AlgHom.id (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)))
      (fun _ _ => Commute.all _ _)) (compAt L s.v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [GlobalTheory.SplitLift.proj_tmul, GlobalTheory.InertUmax.compAt_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

theorem loc_eq_one_of_compAt' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    (x : GAf L n) (h : (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = 1) : s.loc n x = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  have e := congrFun (congrFun h a) b
  simp only [Matrix.map_apply] at e
  change s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) a b) = (1 : Matrix (Fin n) (Fin n) _) a b
  rw [proj_eq_comp, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isLiftN_map' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hcs : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) (r q : ℕ) (g : GL (Fin r) (ZMod q))
    (M : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (hM : IsLiftAt s r q g M) :
    IsLiftN g (Matrix.GeneralLinearGroup.map c.toRingHom M) := by
  have hv := GlobalTheory.SplitConjVal.valuation_eq s c hc hcs
  intro a b
  have h := hM a b
  split_ifs at h ⊢ with hab
  · rw [GlobalTheory.BlockConj.valued_lt_one_iff_w]
    have e : (Matrix.GeneralLinearGroup.map c.toRingHom M).val a b -
        (((g : Matrix (Fin r) (Fin r) (ZMod q)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val : s.w.adicCompletion L) =
        c (M.val a b - (((g : Matrix (Fin r) (Fin r) (ZMod q)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val :
          s.v.adicCompletion (maximalRealSubfield L))) := by
      rw [map_sub, map_natCast]; rfl
    rw [e, hv]; exact h
  · change c (M.val a b) = 1
    rw [h, map_one]
  · change c (M.val a b) = 0
    rw [h, map_zero]

end GlobalTheory.LiftOther

namespace GlobalTheory.LiftOther

theorem gPl_finite (D : D7) : (PendOf.gPl D).Finite := by
  classical
  choose S hS using GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D
  refine (Set.finite_range fun kv => (S kv).v).subset ?_
  rintro w ⟨kv, hkv⟩
  refine ⟨kv, HeightOneSpectrum.ext ?_⟩
  rw [← (S kv).w_under, hS kv]
  exact hkv

theorem over_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (h : NG.OverPl s.w w) : s.v = w :=
  HeightOneSpectrum.ext (s.w_under.symm.trans h)

theorem map_inv_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x y : GAf L n) : ((x⁻¹ * y).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) =
      ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) * (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  rw [← Matrix.map_mul]; rfl

theorem map_inv_mul_self {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : GAf L n) : ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) * (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1 := by
  rw [← map_inv_mul, inv_mul_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.LiftOther
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CocycleNat

theorem exists_pow_smul_mem {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G]
    (T : LocLat G ℚ_[l] K O) (v : T.V) : ∃ n : ℕ, (l : K) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.NatCastNormLtOne.main
  | exact _root_.GlobalTheory.NatCastNormLtOne.main
  | (apply _root_.GlobalTheory.NatCastNormLtOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastNormLtOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastNormLtOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastNormLtOne.main ..)

end GlobalTheory.CocycleNat

noncomputable section

namespace GlobalTheory.CocycleNat

theorem actB_map {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [Algebra O K]
    [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G] (s : G →* GQ l)
    {T₁ T₂ : LocLat G ℚ_[l] K O} (f : LatHom T₁.L T₂.L) (g : G) (z : TW (OB l O) T₁) :
    TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (actB s T₁ g z) =
      actB s T₂ g (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r x =>
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
    congr 1
    exact Subtype.ext (f.equiv g x)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.CocycleNat

namespace GlobalTheory.CocycleNat

theorem main (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ)
    (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (T₁ T₂ : LocLat (Gl l) ℚ_[l] K O)
    (R₁ : GalDat t ϖ (sQ l) D₁ T₁) (R₂ : GalDat t ϖ (sQ l) D₂ T₂) (f : LatHom T₁.L T₂.L) (F : BKHom D₁ D₂) :
    IsMapOf R₁.I R₂.I f F.toHom → ∀ y c, R₁.ClassOf y c → R₂.ClassOf (F.app y) (f.post c) := by
  intro hF y c hc
  obtain ⟨b, ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, hb⟩, hcob⟩ := hc
  have N := GlobalTheory.T.bcrisTensorIdentification_natural l a e O K t ϖ ι D₁.toPhiMod T₁ R₁.I R₁.jB R₁.cmp κ D₂.toPhiMod T₂ R₂.I R₂.jB f
    F.toHom R₂.cmp hF
  set Φ := TensorProduct.map (R := O) (LinearMap.id (R := O) (M := OB l O))
    ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  have hy' : F.app y ∈ ME D₂.toPhiMod := F.app_mem_Mext (le_away _ _) hy
  have hσ' : F.app σ.1 ∈ D₂.MMl := F.toHom.app_mem_ext ((A_le_S (l := l) (e := e)).trans (le_away _ _)) σ.2
  refine ⟨Φ b, ⟨hy', homW t ϖ F.toHom m₀, ⟨F.app σ.1, hσ'⟩, Φ b₀, ?_, F.app_mem_inv h2, ?_, ?_, ?_⟩, ?_⟩
  · rw [← homW_phiW, ← map_sub, h1, homW_toW]
  · change D₂.conn (F.app σ.1) = D₂.zeta (F.app y)
    rw [← F.toHom.app_conn, h3, F.toHom.app_zeta]
  · have := N.2 _ _ h4
    rwa [homW_phiW] at this
  · rw [hb, map_sub, N.1 σ ⟨F.app σ.1, hσ'⟩ rfl]
  · intro g n x' hx'
    obtain ⟨N', hN'⟩ := exists_pow_smul_mem T₁ (c g)
    have hc2 := congrArg Φ (hcob g N' ⟨_, hN'⟩ rfl)
    rw [map_smul, map_sub, actB_map, hΦ, TensorProduct.map_tmul, LinearMap.id_apply] at hc2
    rw [← hΦ] at hc2
    have hsm : ∀ (k : ℕ) (v : T₂.V), ((l : O) ^ k) • v = (l : K) ^ k • v := fun k v => by
      rw [← algebraMap_smul K ((l : O) ^ k) v, map_pow, map_natCast]
    have hx'' : (l : O) ^ N' • x' = (l : O) ^ n • ((f.f.restrictScalars O).restrict f.T_le ⟨_, hN'⟩) := by
      apply Subtype.ext
      change (l : O) ^ N' • (x' : T₂.V) = (l : O) ^ n • f.f ((l : K) ^ N' • c g)
      rw [hx', hsm, hsm, map_smul, smul_smul, smul_smul, mul_comm]
      rfl
    have key : ∀ z w : TW (OB l O) T₂, (l : O) ^ N' • z = (l : O) ^ N' • w → z = w := by
      intro z w h
      have hu : IsUnit ((l : OB l O) ^ N') := by
        have := (GlobalTheory.MemLoc.isUnit_l_Bcris l).map
          (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        rw [map_natCast] at this
        exact this.pow N'
      rw [← algebraMap_smul (OB l O) ((l : O) ^ N') z, ← algebraMap_smul (OB l O) ((l : O) ^ N') w,
        map_pow, map_natCast] at h
      exact hu.smul_left_cancel.1 h
    apply key
    rw [← TensorProduct.tmul_smul, hx'', TensorProduct.tmul_smul, hc2, smul_comm]

end GlobalTheory.CocycleNat
end
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.CocycleInt

theorem TWincl_comp_toB {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K]
    [Algebra O K] [NormedAlgebra ℚ_[l] K] {T : LocLat (Gl l) ℚ_[l] K O} (z : TW (OA l O) T) :
    TWincl (toOB l O) T (TWincl (toOCr l O) T z) = TWincl (toB l O) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul r x => rfl

theorem TWincl_smul' {O R R' G Qp LL : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    [Group G] [TopologicalSpace G] [Field Qp] [Field LL] [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL]
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

end GlobalTheory.BKGal.CocycleInt


open GlobalTheory.BKGal.CocycleInt in
theorem GlobalTheory.BKGal.potential_cocycle_mem_lpow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, ∀ c : ℕ, (l : K) ^ c • D.zeta y ∈ D.MM → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → (∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x) → ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R hηH hl y hyY c hc b hb g hg hex
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).1
  obtain ⟨hy, m₀, σ, b₀, hm₀, -, hconn, hval, rfl⟩ := hb
  have hl2 : l ≠ 2 := by omega
  obtain ⟨z, hz⟩ := GlobalTheory.T.prime_pow_galois_sub_one_mem_tensorAcris_image l a e O K t ϖ hl2 ι η H D T R σ c (by rw [hconn]; exact hc) g hg
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.T.mu_pow_smul_acrisLattice_mem_acrisTensor l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower R.jB R.cmp ε hε z
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.muPow_smul_crystallineValue_mem_ainfLattice l a e O K t ϖ ι η H D T R y hyY hy m₀ b₀ hm₀ hval ε hε
  obtain ⟨z₁, hz₁⟩ := GlobalTheory.T.muOf_pow_smul_actB_sub_self_mem_range_TWincl l O K T g ε hε (H + 2 * η) b₀ z₀ hz₀
  obtain ⟨n, x, hx⟩ := hex
  set jσ := R.jB (toBcris t ϖ D.toPhiMod σ)
  refine GlobalTheory.T.pow_smul_mem_lattice_of_acris_bound l O K T hl2 ε hε (H + 2 * η) n c (by omega) _ x
    (toOCr l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + η)) • w₁ - (l : O) ^ c • TWincl (toOCr l O) T z₁) hx ?_
  have hsplit : actB (sQ l) T g (jσ - b₀) - (jσ - b₀) = (actB (sQ l) T g jσ - jσ) - (actB (sQ l) T g b₀ - b₀) := by
    rw [map_sub]; abel
  have hmu : ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η) : OA l O) =
      ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + η)) * ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ η) := by
    rw [show H + 2 * η = (H + η) + η by ring, pow_add]
  rw [hsplit, map_sub, TWincl_smul', map_smul, TWincl_comp_toB, ← hz₁, smul_sub, hz, ← hw₁]
  rw [smul_sub, hmu, map_mul, mul_smul, hw₁, smul_comm ((l : O) ^ c) (toB l O _ * toB l O _ : OB l O)]
  rfl
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.IntConnTaylor

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∃ C : Conn P, C.nabla = P.nabla ∧ Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C := by
  intro hBS l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I hBK
  obtain ⟨sh, φ₂, h1, h2, h3⟩ := GlobalTheory.T.exists_taylorShift_frobenius_twoVariable_compatible l (↥LL.1)
  obtain ⟨ε, hε0, hεφ, hεS⟩ := GlobalTheory.T.exists_integral_crystal_stratification_matrix hBS l a e ϖ LL hl2 ι P T I hBK sh φ₂ h1 h2 h3
  have hc := GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow (↥(OL LL)) (↥LL.1) l e a ι P sh φ₂ h1 h2 h3 ε hε0 hεφ
  have hphi : ∀ j, P.phi (bas j) ∈ P.MM := fun j =>
    P.ext_mono (fun _ h => A_le_S l e h) (P.phi_mem_L (P.bas_mem_M j))
  have hpow : ∀ (n : ℕ) (j : ι), (P.nabla ^ n) (P.phi (bas j)) ∈ P.MM := fun n j =>
    mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => by rw [← hc τ n i j]; exact hεS τ i j n
  have hMM : ∀ m ∈ P.MM, P.nabla m ∈ P.MM := fun m hm =>
    P.nabla_mem_MM_of_basis (fun j => by simpa using hpow 1 j) hphi hm
  let C : Conn P := ⟨P.nabla, fun f v => P.nabla_smul_tot f v, hMM⟩
  have hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k *
      (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e := fun τ j k i =>
    mul_mem (pow_mem (uIn (S (↥(OL LL)) (↥LL.1) e)).2 k)
      (P.mem_extc_iff.1 (mem_tot.1 (hpow k j) τ) i)
  exact ⟨C, rfl, GlobalTheory.T.galois_taylor_formula_breuilKisin_lattice l a e ϖ LL hl2 ι P _ _ C hS (GlobalTheory.T.galois_dividedTaylor_expansion_frobeniusBasis hBS l a e ϖ LL hl2 ι P T I hBK hS)⟩

end GlobalTheory.IntConnTaylor
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section
namespace GlobalTheory.BSP.HeightSprime

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∃ (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ K bk τ hτ d ρ hρ s Y hY hP
  obtain ⟨ι, TB, k, v, Z, hnull, hWZ, hsum⟩ := GlobalTheory.T.exists_bounded_periods_disc_ainf l K bk τ hτ d ρ hρ s
  have hcol : ∀ i (b : Fin d), ∃ c : Fin d → bk.S, (fun a => v i a b) = Y *ᵥ fun a => bk.ev (c a) := by
    intro i b
    refine (hP _).1 ⟨fun a => Z i a b, fun j hj => ?_⟩
    funext a
    have h := congrFun (congrFun (hWZ j hj i) a) b
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h
  choose σc hσc using hcol
  set σ : ι → Matrix (Fin d) (Fin d) bk.S := fun i => Matrix.of fun a b => σc i b a with hσdef
  have hv : ∀ i, v i = Y * (σ i).map bk.ev := by
    intro i
    refine Matrix.ext fun a b => ?_
    have h := congrFun (hσc i b) a
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, σ] using h
  have hσn := GlobalTheory.T.null_powerSeries_of_null_ainf_mul l K bk ι TB d Y hY σ (fun n a b => by simpa only [← hv] using hnull n a b)
  have hL : ∀ c b : Fin d, ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, bk.ev (σ i c b) * TB.b i ∈ (bk.J ^ n).map bk.ev :=
    fun c b => GlobalTheory.T.breuilKisin_exists_adic_sum_of_null_family l K bk ι TB (fun i => σ i c b) (fun n => hσn n c b)
  choose L hL using hL
  refine ⟨k, Matrix.of L, ?_⟩
  refine Matrix.ext fun a b => ?_
  refine GlobalTheory.T.ainf_jAdic_limit_eq_disc_sum l K bk ι TB (fun i => v i a b * TB.b i) _ _ ?_ ?_
  · simpa [Matrix.smul_apply, Matrix.one_apply] using hsum a b
  · classical
    intro n
    choose F hF using fun c => hL c b n
    refine ⟨Finset.univ.biUnion F, fun G hG => ?_⟩
    have e : (Y * Matrix.of L) a b - ∑ i ∈ G, v i a b * TB.b i =
        ∑ c, Y a c * (L c b - ∑ i ∈ G, bk.ev (σ i c b) * TB.b i) := by
      simp only [hv, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
        Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _
      (hF c G ((Finset.subset_biUnion_of_mem F (Finset.mem_univ c)).trans hG))
end GlobalTheory.BSP.HeightSprime
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} {R : Type} [CommRing R]

theorem FHom.ext_u {M M' : FCrys l R} {u u' : FHom M M'} (h : ∀ P, u.u P = u'.u P) : u = u' := by
  cases u; cases u'
  congr
  funext P
  exact h P

theorem FHom.eq_of_tr {M M' : FCrys l R} (u u' : FHom M M') {P Q : Obj l R} (g : Hom P Q)
    (hP : u.u P = u'.u P) : u.u Q = u'.u Q := by
  let v : M.M P →ₛₗ[g.f] M'.M Q := (M'.tr g).comp (u.u P)
  obtain ⟨w, -, hw⟩ := M.tr_bc g (M'.M Q) v
  have h1 := hw (u.u Q) fun x => by simp [v, u.u_tr]
  have h2 := hw (u'.u Q) fun x => by simp [v, u'.u_tr, hP]
  rw [h1, h2]

theorem FHom.eq_of_inj {M M' : FCrys l R} (u u' : FHom M M') {B C : Obj l R} (h : Hom B C)
    (hinj : Function.Injective h.f) (hC : u.u C = u'.u C) : u.u B = u'.u B := by
  haveI := M'.fin B
  haveI := M'.proj B
  have hi : Function.Injective (M'.tr h) :=
    semiBC_injective_of_injective _ _ h.f hinj _ _ (M'.tr h) (M'.tr_bc h)
  ext x
  apply hi
  rw [← u.u_tr, ← u'.u_tr, hC]

theorem fhom_ext_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M M' : FCrys l ↥(OL K))
    (u u' : FHom M M'), u.u bk.prism = u'.u bk.prism → u = u' := by
  intro l _ K bk M M' u u' hbk
  apply FHom.ext_u
  intro B
  obtain ⟨C, h, ⟨g⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  have hC := FHom.eq_of_tr u u' g hbk
  exact FHom.eq_of_inj u u' h (GlobalTheory.T.prism_cover_injective_and_descent l _ B C h hc).1 hC

end GlobalTheory.BSP
end
end
