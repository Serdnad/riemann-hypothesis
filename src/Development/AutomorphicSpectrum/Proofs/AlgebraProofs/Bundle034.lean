module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Twomega
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle015
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle028
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
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle010

@[expose] public section

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : (∀ k, ι k) → AddSubgroup V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), QuotExact O x A A' E.lat E'.lat C.lat C'.lat → ∃ E'' : ChartBundle O (mseg x) N V, LatLE O x E' E'' ∧ LatLE O x E'' E ∧ QuotEquiv O x A A' E''.lat E'.lat ∧ QuotEquiv O x E.lat E''.lat C.lat C'.lat := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N₀ N N₂ V₀ _ _ V _ _ V₂ _ _ A A' E E' C C' hQ
  obtain ⟨Γ, Δ, hΓ, hΔ, hX⟩ := hQ
  have bundleOfFamily : ∀ (N : ℕ) (W : Type) [AddCommGroup W] [Module Ω W],
      (∀ Γ : (∀ k, ι k) → AddSubgroup W, IsLatFamily O x Γ →
        (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) →
        ∃ E : ChartBundle O (mseg x) N W, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧
      ∀ E : ChartBundle O (mseg x) N W, IsLatFamily O x E.lat ∧
        ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) := by
    classical
    intro N W _ _
    refine ⟨fun Γ hfam hloc => ?_, fun E => ⟨⟨fun s _ => E.stable s, fun s t hs ht => E.overlap s t hs ht⟩, fun s hs => ⟨E.stable s, E.frame s hs⟩⟩⟩
    refine ⟨{ lat := fun s => if mseg x s = 0 then ⊥ else Γ s
              stable := ?_
              frame := ?_
              overlap := ?_ }, ?_⟩
    · intro s a ha e he
      by_cases h : mseg x s = 0
      · simp only [h, if_true, AddSubgroup.mem_bot] at he ⊢
        rw [he, smul_zero]
      · simp only [h, if_false] at he ⊢
        exact hfam.1 s h a ha e he
    · intro s hs
      simp only [hs, if_false]
      exact (hloc s hs).2
    · intro s t hs ht e he
      simp only [hs, ht, if_false] at he ⊢
      exact hfam.2 s t hs ht e he
    · intro s hs
      simp only [hs, if_false]
  obtain ⟨F, hF⟩ : ∃ F : (∀ k, ι k) → AddSubgroup V,
      F = fun s => (Δ s).comap (AddMonoidHom.inl V V₂) := ⟨_, rfl⟩
  have memF : ∀ s b, b ∈ F s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s b
    subst hF
    exact Iff.rfl
  have hFlat : IsLatFamily O x F := by
    refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
    · have h := hΔ.1.1 s hs a ha (v, 0) ((memF s v).1 hv)
      rw [memF]
      simpa using h
    · obtain ⟨m, hm⟩ := hΔ.1.2 s t hs ht (v, 0) ((memF s v).1 hv)
      refine ⟨m, ?_⟩
      rw [memF]
      simpa using hm
  have hFfree : ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (F s) := by
    intro s hs
    have hE := ((bundleOfFamily N V).2 E).2 s hs
    have hC := ((bundleOfFamily N₂ V₂).2 C).2 s hs
    have hC' := ((bundleOfFamily N₂ V₂).2 C').2 s hs
    have h := (GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel.main (chartRing O (mseg x) s) N N₂ (E.lat s) (C.lat s)
      (C'.lat s) (Δ s) hE hC hC' (fun a ha v hv => hΔ.1.1 s hs a ha v hv)
      (fun v w h => (hΔ.2 s hs).1 v w h) (fun v hv => (hΔ.2 s hs).2.1 v hv)
      (fun w => (hΔ.2 s hs).2.2.1 w) (fun w hw => (hX s hs).2.1 w hw)).2
    rw [hF]
    exact h
  obtain ⟨E'', hE''⟩ := (bundleOfFamily N V).1 F hFlat hFfree
  have memE'' : ∀ s, mseg x s ≠ 0 → ∀ b, b ∈ E''.lat s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s hs b
    rw [hE'' s hs, memF]
  refine ⟨E'', fun s hs b hb => ?_, fun s hs b hb => ?_,
    ⟨Γ, ⟨hΓ.1, fun s hs => ⟨fun v w h => ⟨((hΓ.2 s hs).1 v w h).1,
        (memE'' s hs w).2 (((hX s hs).2.2 w).2 ⟨v, h⟩)⟩,
      (hΓ.2 s hs).2.1, (hΓ.2 s hs).2.2.1, (hΓ.2 s hs).2.2.2⟩⟩,
      fun s hs => ⟨(hX s hs).1, fun w hw => ((hX s hs).2.2 w).1 ((memE'' s hs w).1 hw)⟩⟩,
    ⟨Δ, ⟨hΔ.1, fun s hs => ⟨(hΔ.2 s hs).1, (hΔ.2 s hs).2.1, (hΔ.2 s hs).2.2.1,
        fun v hv => (memE'' s hs v).1 hv⟩⟩,
      fun s hs => ⟨fun v hv => (memE'' s hs v).2 hv, (hX s hs).2.1⟩⟩⟩
  · exact (memE'' s hs b).2 ((hΔ.2 s hs).2.2.2 b hb)
  · exact ((hΔ.2 s hs).1 b 0 ((memE'' s hs b).1 hb)).1

end GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tower_omega : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) [Module.Free O L] [Module.Finite O L] (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), ∃ j : G.omega ≃ₗ[O] Module.Dual O L, (∀ (χ : G.dual.Tate) n, X.der n (e n (charElem χ n)).1 (j (dlog G χ))) ∧ ∀ (φ : La →+ La) (dφ : L →ₗ[O] L) (f : G ⟶ G), X.Acts φ dφ → (∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) → ∀ w, j (omegaMap G G f w) = j w ∘ₗ dφ :=
  by
    intro p _ C _ _ _ v O _ _ _ _ _ hO La _ _ _ L _ _ X _ _ G e τ hre
    have counit_eq (n : ℕ) (a : G.A n) :
        Bialgebra.counitAlgHom O (G.A n) a = (e n a).1 1 := by
      have h := hre.pt 0 n a
      rw [map_zero] at h
      exact h
    have mem_sq_iff (n : ℕ) (a : G.A n) :
        a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 ↔
          e n a ∈ BT.augIdeal (X.A n) ^ 2 := by
      have hker : (BT.augIdeal (X.A n)).comap (e n) =
          RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
        ext b
        rw [Ideal.mem_comap, OrderApi.mem_augIdeal, RingHom.mem_ker, counit_eq]
      have hmap : (RingHom.ker (Bialgebra.counitAlgHom O (G.A n))).map (e n) =
          BT.augIdeal (X.A n) := by
        rw [← hker, Ideal.map_comap_of_surjective _ (e n).surjective]
      rw [← hmap, ← Ideal.map_pow]
      constructor
      · exact Ideal.mem_map_of_mem _
      · intro h
        obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective _ (e n).surjective).1 h
        rwa [← (e n).injective hab]
    have dUnit_eq_zero_iff (n : ℕ) (a : G.A n) :
        PDiv.dUnit (R := O) a = 0 ↔ X.der n (e n a).1 0 := by
      rw [PDiv.dUnit, AugCot.d_eq_zero_iff, mem_sq_iff, map_sub, AlgEquiv.commutes]
      set c := Bialgebra.counitAlgHom O (G.A n) a with hc
      have hc' : X.der n (algebraMap O (X.A n) c).1 0 := X.der_const n c
      constructor
      · intro h
        have hd := PositivityTheory.HtPt.Twomega.der_of_mem_sq X n _ h
        simpa using X.der_add n _ _ _ _ hd hc'
      · intro h
        have hd := PositivityTheory.HtPt.Twomega.der_sub X n _ _ _ _ h hc'
        rw [sub_zero] at hd
        refine X.der_zero n ⟨e n a - algebraMap O (X.A n) c, ?_⟩ hd
        rw [OrderApi.mem_augIdeal, hc, counit_eq]
        exact sub_self _
    have dUnit_eq_iff (n : ℕ) (a b : G.A n) (w : Module.Dual O L)
        (h : X.der n (e n a).1 w) : PDiv.dUnit (R := O) b = PDiv.dUnit (R := O) a ↔ X.der n (e n b).1 w := by
      rw [← sub_eq_zero, PDiv.dUnit, PDiv.dUnit, ← map_sub]
      refine (dUnit_eq_zero_iff n (b - a)).trans ?_
      rw [map_sub]
      constructor
      · intro hd
        simpa using X.der_add n _ _ _ _ hd h
      · intro hd
        have hsub := PositivityTheory.HtPt.Twomega.der_sub X n _ _ _ _ hd h
        rwa [sub_self] at hsub
    have exists_der (n : ℕ) (w : Module.Dual O L) : ∃ a : G.A n, X.der n (e n a).1 w := by
      obtain ⟨f, hf, h⟩ := X.der_onto n w
      exact ⟨(e n).symm ⟨f, hf⟩, by rwa [AlgEquiv.apply_symm_apply]⟩
    let cls (n : ℕ) (w : Module.Dual O L) := PDiv.dUnit (R := O) (exists_der n w).choose
    have dUnit_eq_cls (n : ℕ) (a : G.A n) (w : Module.Dual O L) :
        PDiv.dUnit (R := O) a = cls n w ↔ X.der n (e n a).1 w :=
      dUnit_eq_iff n _ a w (exists_der n w).choose_spec
    have der_res (n : ℕ) (a : G.A (n + 1)) (w : Module.Dual O L)
        (h : X.der (n + 1) (e (n + 1) a).1 w) : X.der n (e n (G.res n a)).1 w :=
      X.der_res n _ _ w h (hre.res n a)
    let toOmega : Module.Dual O L →ₗ[O] G.omega :=
      { toFun := fun w => ⟨fun n => cls n w, fun n => by
          obtain ⟨a, ha⟩ := exists_der (n + 1) w
          change PDiv.cotMap (G.res n) (cls (n + 1) w) = cls n w
          rw [← (dUnit_eq_cls _ a w).2 ha, PDiv.cotMap_d, dUnit_eq_cls]
          exact der_res n a w ha⟩
        map_add' := fun w w' => Subtype.ext (funext fun n => by
          obtain ⟨a, ha⟩ := exists_der n w
          obtain ⟨b, hb⟩ := exists_der n w'
          change cls n (w + w') = cls n w + cls n w'
          rw [← (dUnit_eq_cls _ a w).2 ha, ← (dUnit_eq_cls _ b w').2 hb,
            PDiv.dUnit, PDiv.dUnit, ← map_add (f := _), eq_comm]
          refine (dUnit_eq_cls _ _ _).2 ?_
          rw [map_add (f := _)]
          exact X.der_add n _ _ _ _ ha hb)
        map_smul' := fun r w => Subtype.ext (funext fun n => by
          obtain ⟨a, ha⟩ := exists_der n w
          change cls n (r • w) = r • cls n w
          rw [← (dUnit_eq_cls _ a w).2 ha, PDiv.dUnit, ← map_smul, eq_comm]
          refine (dUnit_eq_cls _ _ _).2 ?_
          rw [map_smul]
          exact PositivityTheory.HtPt.Twomega.der_smul X n r _ _ ha) }
    have toOmega_val (w : Module.Dual O L) (n : ℕ) : (toOmega w).1 n = cls n w := rfl
    have toOmega_bijective : Function.Bijective toOmega := by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro w hw
        refine PositivityTheory.HtPt.Twomega.eq_zero_of_cong hO w fun n => ?_
        have h0 : PDiv.dUnit (R := O) (0 : G.A n) = 0 := map_zero _
        have h1 : cls n w = 0 := congrArg (fun x : G.omega => x.1 n) hw
        exact (X.der_unique n _ 0 w ((dUnit_eq_zero_iff n 0).1 h0)).1
          ((dUnit_eq_cls n 0 w).1 (h0.trans h1.symm))
      · intro ω
        choose a ha using fun n => AugCot.d_surjective _ (ω.1 n)
        choose w hw using fun n => X.der_ex n (e n (a n)).1 (e n (a n)).2
        obtain ⟨W, hW⟩ := PositivityTheory.HtPt.Twomega.exists_lim hO w fun n => by
          refine (X.der_unique n _ _ _ (hw n)).1 ?_
          refine (dUnit_eq_iff n _ _ _ (der_res n _ _ (hw (n + 1)))).1 ?_
          rw [← PDiv.cotMap_d, PDiv.dUnit, PDiv.dUnit, ha, ha]
          exact (ω.2 n).symm
        refine ⟨W, Subtype.ext (funext fun n => ?_)⟩
        rw [toOmega_val, ← ha, eq_comm]
        exact (dUnit_eq_cls n _ W).2 ((X.der_unique n _ _ _ (hw n)).2 (hW n))
    let k := LinearEquiv.ofBijective toOmega toOmega_bijective
    have hk (ω : G.omega) (n : ℕ) : ω.1 n = cls n (k.symm ω) :=
      congrArg (fun x : G.omega => x.1 n) (k.apply_symm_apply ω).symm
    refine ⟨k.symm, fun χ n => ?_, fun φ dφ f hφ hf ω => ?_⟩
    · exact (dUnit_eq_cls n _ _).1 (hk (dlog G χ) n)
    · rw [LinearEquiv.symm_apply_eq]
      refine Subtype.ext (funext fun n => ?_)
      obtain ⟨a, ha⟩ := exists_der n (k.symm ω)
      rw [omegaMap_val, hk ω n, ← (dUnit_eq_cls n a _).2 ha, PDiv.cotMap_d]
      exact (dUnit_eq_cls n _ _).2 ((hφ n _ _ (hf n a)).2 _ ha)

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.divisible_group_tower_free : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) [Module.Free O L] [Module.Finite O L] (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), ∃ j : G.omega ≃ₗ[O] Module.Dual O L, (∀ (χ : G.dual.Tate) n, X.der n (e n (charElem χ n)).1 (j (dlog G χ))) ∧ ∀ (φ : La →+ La) (dφ : L →ₗ[O] L) (f : G ⟶ G), X.Acts φ dφ → (∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) → ∀ w, j (omegaMap G G f w) = j w ∘ₗ dφ := by
  intro p _ C _ _ _ v O _ _ _ _ _ hO La _ _ _ L _ _ X _ _ G e τ hre
  have counit_eq (n : ℕ) (a : G.A n) :
      Bialgebra.counitAlgHom O (G.A n) a = (e n a).1 1 := by
    have h := hre.pt 0 n a
    rw [map_zero] at h
    exact h
  have mem_sq_iff (n : ℕ) (a : G.A n) :
      a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 ↔
        e n a ∈ BT.augIdeal (X.A n) ^ 2 := by
    have hker : (BT.augIdeal (X.A n)).comap (e n) =
        RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
      ext b
      rw [Ideal.mem_comap, OrderApi.mem_augIdeal, RingHom.mem_ker, counit_eq]
    have hmap : (RingHom.ker (Bialgebra.counitAlgHom O (G.A n))).map (e n) =
        BT.augIdeal (X.A n) := by
      rw [← hker, Ideal.map_comap_of_surjective _ (e n).surjective]
    rw [← hmap, ← Ideal.map_pow]
    constructor
    · exact Ideal.mem_map_of_mem _
    · intro h
      obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective _ (e n).surjective).1 h
      rwa [← (e n).injective hab]
  have dUnit_eq_zero_iff (n : ℕ) (a : G.A n) :
      PDiv.dUnit (R := O) a = 0 ↔ X.der n (e n a).1 0 := by
    rw [PDiv.dUnit, AugCot.d_eq_zero_iff, mem_sq_iff, map_sub, AlgEquiv.commutes]
    set c := Bialgebra.counitAlgHom O (G.A n) a with hc
    have hc' : X.der n (algebraMap O (X.A n) c).1 0 := X.der_const n c
    constructor
    · intro h
      have hd := PositivityTheory.HtPt.Twomega.der_of_mem_sq X n _ h
      simpa using X.der_add n _ _ _ _ hd hc'
    · intro h
      have hd := PositivityTheory.HtPt.Twomega.der_sub X n _ _ _ _ h hc'
      rw [sub_zero] at hd
      refine X.der_zero n ⟨e n a - algebraMap O (X.A n) c, ?_⟩ hd
      rw [OrderApi.mem_augIdeal, hc, counit_eq]
      exact sub_self _
  have dUnit_eq_iff (n : ℕ) (a b : G.A n) (w : Module.Dual O L)
      (h : X.der n (e n a).1 w) : PDiv.dUnit (R := O) b = PDiv.dUnit (R := O) a ↔ X.der n (e n b).1 w := by
    rw [← sub_eq_zero, PDiv.dUnit, PDiv.dUnit, ← map_sub]
    refine (dUnit_eq_zero_iff n (b - a)).trans ?_
    rw [map_sub]
    constructor
    · intro hd
      simpa using X.der_add n _ _ _ _ hd h
    · intro hd
      have hsub := PositivityTheory.HtPt.Twomega.der_sub X n _ _ _ _ hd h
      rwa [sub_self] at hsub
  have exists_der (n : ℕ) (w : Module.Dual O L) : ∃ a : G.A n, X.der n (e n a).1 w := by
    obtain ⟨f, hf, h⟩ := X.der_onto n w
    exact ⟨(e n).symm ⟨f, hf⟩, by rwa [AlgEquiv.apply_symm_apply]⟩
  let cls (n : ℕ) (w : Module.Dual O L) := PDiv.dUnit (R := O) (exists_der n w).choose
  have dUnit_eq_cls (n : ℕ) (a : G.A n) (w : Module.Dual O L) :
      PDiv.dUnit (R := O) a = cls n w ↔ X.der n (e n a).1 w :=
    dUnit_eq_iff n _ a w (exists_der n w).choose_spec
  have der_res (n : ℕ) (a : G.A (n + 1)) (w : Module.Dual O L)
      (h : X.der (n + 1) (e (n + 1) a).1 w) : X.der n (e n (G.res n a)).1 w :=
    X.der_res n _ _ w h (hre.res n a)
  let toOmega : Module.Dual O L →ₗ[O] G.omega :=
    { toFun := fun w => ⟨fun n => cls n w, fun n => by
        obtain ⟨a, ha⟩ := exists_der (n + 1) w
        change PDiv.cotMap (G.res n) (cls (n + 1) w) = cls n w
        rw [← (dUnit_eq_cls _ a w).2 ha, PDiv.cotMap_d, dUnit_eq_cls]
        exact der_res n a w ha⟩
      map_add' := fun w w' => Subtype.ext (funext fun n => by
        obtain ⟨a, ha⟩ := exists_der n w
        obtain ⟨b, hb⟩ := exists_der n w'
        change cls n (w + w') = cls n w + cls n w'
        rw [← (dUnit_eq_cls _ a w).2 ha, ← (dUnit_eq_cls _ b w').2 hb,
          PDiv.dUnit, PDiv.dUnit, ← map_add (f := _), eq_comm]
        refine (dUnit_eq_cls _ _ _).2 ?_
        rw [map_add (f := _)]
        exact X.der_add n _ _ _ _ ha hb)
      map_smul' := fun r w => Subtype.ext (funext fun n => by
        obtain ⟨a, ha⟩ := exists_der n w
        change cls n (r • w) = r • cls n w
        rw [← (dUnit_eq_cls _ a w).2 ha, PDiv.dUnit, ← map_smul, eq_comm]
        refine (dUnit_eq_cls _ _ _).2 ?_
        rw [map_smul]
        exact PositivityTheory.HtPt.Twomega.der_smul X n r _ _ ha) }
  have toOmega_val (w : Module.Dual O L) (n : ℕ) : (toOmega w).1 n = cls n w := rfl
  have toOmega_bijective : Function.Bijective toOmega := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro w hw
      refine PositivityTheory.HtPt.Twomega.eq_zero_of_cong hO w fun n => ?_
      have h0 : PDiv.dUnit (R := O) (0 : G.A n) = 0 := map_zero _
      have h1 : cls n w = 0 := congrArg (fun x : G.omega => x.1 n) hw
      exact (X.der_unique n _ 0 w ((dUnit_eq_zero_iff n 0).1 h0)).1
        ((dUnit_eq_cls n 0 w).1 (h0.trans h1.symm))
    · intro ω
      choose a ha using fun n => AugCot.d_surjective _ (ω.1 n)
      choose w hw using fun n => X.der_ex n (e n (a n)).1 (e n (a n)).2
      obtain ⟨W, hW⟩ := PositivityTheory.HtPt.Twomega.exists_lim hO w fun n => by
        refine (X.der_unique n _ _ _ (hw n)).1 ?_
        refine (dUnit_eq_iff n _ _ _ (der_res n _ _ (hw (n + 1)))).1 ?_
        rw [← PDiv.cotMap_d, PDiv.dUnit, PDiv.dUnit, ha, ha]
        exact (ω.2 n).symm
      refine ⟨W, Subtype.ext (funext fun n => ?_)⟩
      rw [toOmega_val, ← ha, eq_comm]
      exact (dUnit_eq_cls n _ W).2 ((X.der_unique n _ _ _ (hw n)).2 (hW n))
  let k := LinearEquiv.ofBijective toOmega toOmega_bijective
  have hk (ω : G.omega) (n : ℕ) : ω.1 n = cls n (k.symm ω) :=
    congrArg (fun x : G.omega => x.1 n) (k.apply_symm_apply ω).symm
  refine ⟨k.symm, fun χ n => ?_, fun φ dφ f hφ hf ω => ?_⟩
  · exact (dUnit_eq_cls n _ _).1 (hk (dlog G χ) n)
  · rw [LinearEquiv.symm_apply_eq]
    refine Subtype.ext (funext fun n => ?_)
    obtain ⟨a, ha⟩ := exists_der n (k.symm ω)
    rw [omegaMap_val, hk ω n, ← (dUnit_eq_cls n a _).2 ha, PDiv.cotMap_d]
    exact (dUnit_eq_cls n _ _).2 ((hφ n _ _ (hf n a)).2 _ ha)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.dual_lattice_flag_frame : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), IsDualLat O x β E.lat F.lat → ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → ∀ w₁ : Module.Basis (Fin N) Ω V₁, (∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) → IsFlagFrame x F w₁ (fun j => -b j.rev) :=
  @_root_.PositivityTheory.Xgn.t_flagframe_dual
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

open Coalgebra WithConv

theorem exists_hom_dual_of_pairingExtends : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingExtends B ζ → ∃ lam : G ⟶ G.dual, ∀ (a b : La) n, (e n (charElem (tateMap G G.dual O lam (τ a)) n)).1 (lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X G e τ hre B ζ _ hζ hB
  have sep : ∀ n (f g : G.A n), (∀ a, (τ a).pt n f = (τ a).pt n g) → f = g := fun n f g h =>
    (e n).injective (Subtype.ext (funext fun t => by
      obtain ⟨a, rfl⟩ : ∃ a, lev p n a = t := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
      rw [← hre.pt, ← hre.pt, h]))
  have key : ∀ n, ∃ (lam : CartierDual O (G.A n) →ₐc[O] G.A n) (u : La → G.A n),
      (∀ a φ, (τ a).pt n (lam φ) = φ (u a)) ∧ ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := by
    intro n
    obtain ⟨s, hs, hsv⟩ := hB n
    obtain ⟨l, u, h1, h2⟩ := PositivityTheory.HtPt.Twpol.exists_linear
      (X.A n) (e n) (lev p n) (fun a => (τ a).pt n) (fun a f => hre.pt a n f) s hs
    have h3 : ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := fun a b => (h2 a b).trans (hsv a b)
    obtain ⟨lam, hlam⟩ := PositivityTheory.HtPt.Twpol.exists_bialgHom (fun a => (τ a).pt n) (sep n)
      (by
        change toConv ((τ 0).pt n).toLinearMap = 1
        rw [map_zero]; rfl)
      (fun a b => by
        change toConv ((τ (a + b)).pt n).toLinearMap = _
        rw [map_add (f := _)]; rfl)
      l u h1 (fun b => by simp [h3]) (fun a => by rw [h3]; simp)
      (fun a a' b => by simp [h3, zpow_add]) (fun a b b' => by rw [h3, h3, h3]; simp [zpow_add])
    exact ⟨lam, u, fun a φ => by rw [hlam, h1], h3⟩
  choose lam u h1 h2 using key
  refine ⟨⟨lam, fun n => BialgHom.ext fun φ => sep n _ _ fun a => ?_⟩, fun a b n => ?_⟩
  · change (τ a).pt n (G.res n (lam (n + 1) φ)) = (τ a).pt n (lam n (CartierDual.map (G.mulP n) φ))
    rw [h1, hre.pt, hre.res, ← hre.pt, h1, CartierDual.map_apply]
    refine congrArg _ (sep _ _ _ fun b => ?_)
    rw [TateOver.pt_mulP, h2, h2, ← hζ n, ← zpow_natCast, ← zpow_mul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  · rw [← hre.pt, ← h2]
    refine congrArg _ (CartierDual.eq_of_forall_apply (R := O) fun φ => ?_)
    rw [apply_charElem, tateMap_pt]
    exact h1 n a φ

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
open Coalgebra WithConv


theorem _root_.GlobalTheory.T.divisible_group_tower_dual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingExtends B ζ → ∃ lam : G ⟶ G.dual, ∀ (a b : La) n, (e n (charElem (tateMap G G.dual O lam (τ a)) n)).1 (lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ La _ _ _ L _ _ X G e τ hre B ζ _ hζ hB
  have sep : ∀ n (f g : G.A n), (∀ a, (τ a).pt n f = (τ a).pt n g) → f = g := fun n f g h =>
    (e n).injective (Subtype.ext (funext fun t => by
      obtain ⟨a, rfl⟩ : ∃ a, lev p n a = t :=
        Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
      rw [← hre.pt, ← hre.pt, h]))
  have key : ∀ n, ∃ (lam : CartierDual O (G.A n) →ₐc[O] G.A n) (u : La → G.A n),
      (∀ a φ, (τ a).pt n (lam φ) = φ (u a)) ∧
      ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := by
    intro n
    obtain ⟨s, hs, hsv⟩ := hB n
    obtain ⟨l, u, h1, h2⟩ := PositivityTheory.HtPt.Twpol.exists_linear
      (X.A n) (e n) (lev p n) (fun a => (τ a).pt n) (fun a f => hre.pt a n f) s hs
    have h3 : ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) :=
      fun a b => (h2 a b).trans (hsv a b)
    obtain ⟨lam, hlam⟩ := PositivityTheory.HtPt.Twpol.exists_bialgHom
      (fun a => (τ a).pt n) (sep n)
      (by
        change toConv ((τ 0).pt n).toLinearMap = 1
        rw [map_zero]; rfl)
      (fun a b => by
        change toConv ((τ (a + b)).pt n).toLinearMap = _
        rw [map_add (f := _)]; rfl)
      l u h1 (fun b => by simp [h3]) (fun a => by rw [h3]; simp)
      (fun a a' b => by simp [h3, zpow_add])
      (fun a b b' => by rw [h3, h3, h3]; simp [zpow_add])
    exact ⟨lam, u, fun a φ => by rw [hlam, h1], h3⟩
  choose lam u h1 h2 using key
  refine ⟨⟨lam, fun n => BialgHom.ext fun φ => sep n _ _ fun a => ?_⟩, fun a b n => ?_⟩
  · change (τ a).pt n (G.res n (lam (n + 1) φ)) = (τ a).pt n (lam n (CartierDual.map (G.mulP n) φ))
    rw [h1, hre.pt, hre.res, ← hre.pt, h1, CartierDual.map_apply]
    refine congrArg _ (sep _ _ _ fun b => ?_)
    rw [TateOver.pt_mulP, h2, h2, ← hζ n, ← zpow_natCast, ← zpow_mul, map_nsmul,
      LinearMap.smul_apply, nsmul_eq_mul]
  · rw [← hre.pt, ← h2]
    refine congrArg _ (CartierDual.eq_of_forall_apply (R := O) fun φ => ?_)
    rw [apply_charElem, tateMap_pt]
    exact h1 n a φ
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.power_series_pow_p_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d n : ℕ) (f : PS R n d), f ^ p = ev (fun j => ptPow R d p j) (MvPowerSeries.map (frobenius R p) f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_eq_ev_frobenius | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_eq_ev_frobenius | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_eq_ev_frobenius <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.degree_additive_sub_quotient : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V), IsBun C L → deg C L = subDeg C L W + deg C (quot C L W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot | exact GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot <;> assumption)
end
