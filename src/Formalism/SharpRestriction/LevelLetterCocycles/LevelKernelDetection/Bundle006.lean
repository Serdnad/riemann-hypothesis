module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

section General

variable {LL Qp : Type} [Field LL] [Field Qp] [Algebra Qp LL]
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
  [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
  {B₁ B₂ : Type} [AddCommGroup B₁] [Module Qp B₁] [AddCommGroup B₂] [Module Qp B₂]

theorem pfMapFl_map_comm (f : V₁ →ₗ[LL] V₂) (g : B₁ →ₗ[Qp] B₂) (z : V₁ ⊗[Qp] B₁) :
    AlgebraTensorModule.map f (LinearMap.id : B₂ →ₗ[Qp] B₂)
        (AlgebraTensorModule.map (LinearMap.id : V₁ →ₗ[LL] V₁) g z) =
      AlgebraTensorModule.map (LinearMap.id : V₂ →ₗ[LL] V₂) g
        (AlgebraTensorModule.map f (LinearMap.id : B₁ →ₗ[Qp] B₁) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

section Filt

variable {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)

abbrev pfMapFl_Fb : T₁.V ⊗[Qp] B →ₗ[LL] T₂.V ⊗[Qp] B :=
  AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B)

abbrev pfMapFl_FdR : T₁.V ⊗[Qp] BdR →ₗ[LL] T₂.V ⊗[Qp] BdR :=
  AlgebraTensorModule.map F.f (LinearMap.id : BdR →ₗ[Qp] BdR)

theorem pfMapFl_ιV (z : T₁.V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F z) =
      pfMapFl_FdR F (ιV PD (LL := LL) (V := T₁.V) z) :=
  (pfMapFl_map_comm F.f (PD.ι.toLinearMap.restrictScalars Qp) z).symm

theorem pfMapFl_φ (z : T₁.V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F z) =
      pfMapFl_Fb F (φVB PD (LL := LL) (V := T₁.V) z) :=
  (pfMapFl_map_comm F.f PD.φ.toLinearMap z).symm

theorem pfMapFl_φpow (s : ℕ) (z : T₁.V ⊗[Qp] B) :
    ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ s)
        (pfMapFl_Fb F z) =
      pfMapFl_Fb F (((φVB PD (LL := LL) (V := T₁.V) : Module.End LL (T₁.V ⊗[Qp] B)) ^ s) z) := by
  induction s generalizing z with
  | zero => rfl
  | succ s ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, pfMapFl_φ, ih]

theorem pfMapFl_act (g : G) (z : T₁.V ⊗[Qp] B) :
    actVB PD T₂.ρ g (pfMapFl_Fb F z) = pfMapFl_Fb F (actVB PD T₁.ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [actVB, F.equiv]
  | add x y hx hy =>
    simp only [map_add (f := _)]
    rw [hx, hy]

theorem pfMapFl_dcris (z : T₁.V ⊗[Qp] B) (hz : z ∈ Dcris PD T₁.ρ) :
    pfMapFl_Fb F z ∈ Dcris PD T₂.ρ := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz ⊢
  intro g
  rw [pfMapFl_act, hz g]

theorem pfMapFl_dcrisL (τ₀ : K₀ →ₐ[Qp] LL) (z : T₁.V ⊗[Qp] B) (hz : z ∈ DcrisL PD T₁.ρ τ₀) :
    pfMapFl_Fb F z ∈ DcrisL PD T₂.ρ τ₀ := by
  rw [DcrisL, Submodule.mem_inf] at hz ⊢
  refine ⟨pfMapFl_dcris F z hz.1, ?_⟩
  have h2 := hz.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at h2 ⊢
  intro c
  have h3 : mulVB (K₀ := K₀) (B := B) (V := T₂.V) (LL := LL) c (pfMapFl_Fb F z) =
      pfMapFl_Fb F (mulVB (K₀ := K₀) (B := B) (V := T₁.V) (LL := LL) c z) :=
    (pfMapFl_map_comm F.f (LinearMap.mulLeft Qp (algebraMap K₀ B c)) z).symm
  rw [h3, h2 c, map_smul]

theorem pfMapFl_filV (a : ℤ) (z : T₁.V ⊗[Qp] BdR) (hz : z ∈ FilV PD (LL := LL) (V := T₁.V) a) :
    pfMapFl_FdR F z ∈ FilV PD (LL := LL) (V := T₂.V) a := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨AlgebraTensorModule.map F.f LinearMap.id w,
    (pfMapFl_map_comm F.f ((PD.Fil a).restrictScalars Qp).subtype w).symm⟩

theorem pfMapFl_filCris (a : ℤ) (z : T₁.V ⊗[Qp] B) (hz : z ∈ FilCris PD T₁.ρ a) :
    pfMapFl_Fb F z ∈ FilCris PD T₂.ρ a := by
  rw [FilCris, Submodule.mem_inf, Submodule.mem_comap] at hz ⊢
  refine ⟨pfMapFl_dcris F z hz.1, ?_⟩
  rw [pfMapFl_ιV]
  exact pfMapFl_filV F a _ hz.2

theorem pfMapFl_filD {c : ZMod n} (h : MemD W F c) (s : ℕ) (u : ℤ) (x : Dc W T₁ c)
    (hx : x ∈ FilD W T₁ c s u) : dmapOf h x ∈ FilD W T₂ c s u := by
  have hx' : ιV PD (LL := LL) (V := T₁.V) (x : T₁.V ⊗[Qp] B) ∈ FilLev W T₁ c s u := hx
  obtain ⟨y', hy', hxy⟩ := Submodule.mem_map.1 hx'
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hy'
  show ιV PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F (x : T₁.V ⊗[Qp] B)) ∈ FilLev W T₂ c s u
  refine Submodule.mem_map.2 ⟨_, Submodule.mem_map.2 ⟨pfMapFl_Fb F y,
    ⟨pfMapFl_filCris F u y hy.1, pfMapFl_dcrisL F _ y hy.2⟩, rfl⟩, ?_⟩
  rw [pfMapFl_φpow, pfMapFl_ιV, pfMapFl_ιV, hxy]

end Filt

section Xi

variable {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {c : ZMod n}

theorem pfMapFl_ambF_xi (h : MemD W F c) (s : ℕ) (x : Amb LL (KsW W s) (Dc W T₁ c))
    (hx : x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₁ c) 0)) :
    ambF h s x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₂ c) 0) := by
  have hx' : ∀ i, cf x i ∈ (Tw (LL := LL) (D := Dc W T₁ c) 0 i).baseChange (KsW W s) := hx
  show ∀ i, cf (ambF h s x) i ∈ (Tw (LL := LL) (D := Dc W T₂ c) 0 i).baseChange (KsW W s)
  intro i
  have hi := hx' i
  have hc : cf (ambF h s x) i = (dmapOf h).baseChange (KsW W s) (cf x i) := rfl
  rw [hc]
  unfold Tw at hi ⊢
  split_ifs at hi ⊢ with h0
  · rw [Submodule.baseChange_top]
    exact Submodule.mem_top
  · rw [Submodule.baseChange_bot, Submodule.mem_bot] at hi ⊢
    rw [hi, map_zero]

theorem pfMapFl_mem_FlS {hΔ : DeltaRho hR uZ ιZ c} {ell : ℕ} (Λ f' : PowerSeries O) (s : ℕ)
    (e : LvT hR uZ ιZ T₁ c hΔ ell) :
    e ∈ FlS (hR := hR) (uZ := uZ) (ιZ := ιZ) (T := T₁) (c := c) (hΔ := hΔ) (ell := ell) Λ f' s ↔
      ∃ x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₁ c) 0),
        prL s (Λ • e) = HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s f') • x := Iff.rfl

end Xi

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

theorem mapFl_holds
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ) :
    ∀ s < ell, ∀ e ∈ (lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s,
      prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell e ∈
        (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s := by
  intro s hs e he
  obtain ⟨x, hx, hex⟩ := (pfMapFl_mem_FlS (hΔ := Hy₁.delta)
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) ((baseIdOf hR).Bs.ff' ell j M g) s e).1 he
  refine (pfMapFl_mem_FlS (hΔ := Hy₂.delta)
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) ((baseIdOf hR).Bs.ff' ell j M g) s _).2
    ⟨ambF Mh.memD s x, pfMapFl_ambF_xi Mh.memD s x hx, ?_⟩
  have hsm := (prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell).map_smul
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) e
  erw [← hsm, prL_prEOf Mh s hs, hex, Mh.smul]

theorem cMap_holds (hD : MemD W F c) (kind : ℕ → Kind) (b : ℕ → ℕ) (η : ℕ)
    (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (hLamP : ∀ k, dmapOf hD (lam₁ k) = ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) • lam₂ l) :
    ∀ s < ell, kind s = Kind.up → Formalism.ExponentWindows.E.CMap (UL lam₁ kind b η s) (UL lam₂ kind b η s) P := by
  intro s _ hk w hw
  have hw' : ∑ k, algebraMap O LL (w k) • lam₁ k ∈ FilD W T₁ c s ((b s : ℕ) : ℤ) := by
    have := hw
    simp only [UL, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq,
      hk, UOf] at this
    exact this
  have hmap := pfMapFl_filD F hD s _ _ hw'
  have hsum : dmapOf hD (∑ k, algebraMap O LL (w k) • lam₁ k) =
      ∑ l, algebraMap O LL (P w l) • lam₂ l := by

    rw [map_sum]
    simp only [map_smul, hLamP, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul, ← LinearMap.toMatrix'_mulVec P w]

    simp only [Matrix.mulVec, dotProduct, map_sum]
    refine congrArg (· • lam₂ l) (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul]
    ring
  rw [hsum] at hmap
  show ∑ l, algebraMap O LL (P w l) • lam₂ l ∈ UOf (kind s) (b s) η (FilD W T₂ c s)
  rw [hk]
  exact hmap

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem Pf_KapUnit_prod (hR : Ring9 W) (c : ZMod n) (ell : ℕ) (e : ℕ → ℕ) (s : ℕ)
    (hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s')))) :
    IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ e s'))) := by
  rw [map_prod, map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one ?_
  intro x hx
  rw [map_pow, map_pow]
  exact (hp x (Finset.mem_range.1 hx)).pow _

theorem kapUnit_holds {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {H : ℕ → ℕ} {κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ lam) (j M g η : ℕ)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (m : ℕ)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (k1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (unitsAt : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) :
    ∀ s < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) := by
  intro s hs
  have hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s'))) := by
    intro s' hs'
    by_cases h : s' = s
    · subst h
      obtain ⟨ε, hε⟩ := k1b s' hs
      have hε' : rhoL hR c s' ((baseIdOf hR).Bs.p s') = (ε : PowerSeries (KsW W s')) * PowerSeries.X :=
        hε
      rw [hε', map_mul, HahnSeries.ofPowerSeries_X]
      refine (ε.isUnit.map _).mul (isUnit_iff_exists_inv.2 ⟨HahnSeries.single (-1 : ℤ) 1, ?_⟩)
      rw [HahnSeries.single_mul_single]
      simp
    · exact ((unitsAt s hs).2 s' hs' h).map _
  have hΛ := Pf_KapUnit_prod hR c ell H s hp
  have hP := Pf_KapUnit_prod hR c ell (fun _ => m) s hp
  rw [hκ, map_mul, map_mul]
  refine IsUnit.mul ?_ hP
  rw [Formalism.ExponentWindows.abelian₂]
  exact hΛ

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem rhoC_holds (hR : Ring9 W) (c : ZMod n) (s : ℕ) (a : O) :
    rhoL hR c s (PowerSeries.C a) =
      PowerSeries.C (algebraMap LL (KsW W s) (algebraMap O LL a)) := by
  ext k ζ
  have hC : (PowerSeries.C a : PowerSeries O) = algebraMap O (PowerSeries O) a := by
    rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h1 : PowerSeries.coeff k (rhoL hR c s (PowerSeries.C a)) ζ =
      PowerSeries.coeff k (rhoZ W c ζ ((baseIdOf hR).ι (PowerSeries.C a))) := by
    have h := congrArg (PowerSeries.coeff k) (map_eval_rhoL hR c s (PowerSeries.C a) ζ)
    rw [PowerSeries.coeff_map] at h
    exact h
  rw [h1, hC, AlgHom.commutes, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.coeff_C,
    PowerSeries.coeff_C]
  split_ifs <;> rfl

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

theorem convolution_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (g : ℤ → M) (k : ℤ) :
    ConvolutionAlt.cv (1 : PowerSeries R) g k = g k := by
  unfold ConvolutionAlt.cv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_one, if_neg hj, zero_smul]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

def phiIt (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (m : ℕ) (x : W.DD T) : ℕ → W.DD T
  | 0 => x
  | i + 1 => W.Q ^ m • W.φD T (phiIt W T m x i)

variable {W : LocWach PD LL O v n}

theorem primitive_root_pow_prime {ζ : LL} (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    ∃ j : ℕ, IsPrimitiveRoot (ζ ^ PD.p) (PD.p ^ j) := by
  obtain ⟨j, hj⟩ := hζ
  rcases j with _ | j
  · refine ⟨0, ?_⟩
    rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hj ⊢
    rw [hj, one_pow]
  · refine ⟨j, hj.pow (pow_pos (Fact.out : PD.p.Prime).pos _) ?_⟩
    rw [pow_succ']

theorem phiIt_levB_gen (Lb : LevB W) (T : LocLat G Qp LL O)
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (hp0 : (PD.p : LL) ≠ 0)
    (m : ℕ) (a : ZMod n) (x : W.DD T) :
    ∀ (i : ℕ) (hN : ∀ r ≤ i, phiIt W T m x r ∈ W.N T) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) →
      ∀ k : ℤ, Lb.levB T (a + i) ζ ⟨phiIt W T m x i, hN i le_rfl⟩ k =
        ConvolutionAlt.cv (W.lev (a + i) ζ (∏ r ∈ Finset.range i, W.φA^[r] (W.Q ^ m)))
          (fun k => ((PD.p : LL) ^ ((i : ℤ) * k)) • (φVB PD (LL := LL) (V := T.V))^[i]
            (Lb.levB T a (ζ ^ PD.p ^ i) ⟨x, hN 0 (Nat.zero_le _)⟩ k)) k := by
  intro i
  induction i with
  | zero =>
    intro hN ζ _ k
    rw [Finset.prod_range_zero, map_one, convolution_one]
    simp only [Nat.cast_zero, add_zero, zero_mul, zpow_zero, one_smul, Function.iterate_zero, id, pow_zero,
      pow_one]
    rfl
  | succ i ih =>
    intro hN ζ hζ k
    have hNi : ∀ r ≤ i, phiIt W T m x r ∈ W.N T := fun r hr => hN r (Nat.le_succ_of_le hr)
    have hζp := primitive_root_pow_prime (PD := PD) hζ
    have hstep := levB_φ (a + ((i + 1 : ℕ) : ZMod n)) ζ hζ ⟨phiIt W T m x i, hNi i le_rfl⟩ m (hN (i + 1) le_rfl) k
    have hlet : a + ((i + 1 : ℕ) : ZMod n) - 1 = a + (i : ZMod n) := by push_cast; ring
    rw [hlet] at hstep
    have e0 : (⟨phiIt W T m x (i + 1), hN (i + 1) le_rfl⟩ : ↥(W.N T)) =
        ⟨W.Q ^ m • W.φD T ((⟨phiIt W T m x i, hNi i le_rfl⟩ : ↥(W.N T)) : W.DD T), hN (i + 1) le_rfl⟩ := rfl
    rw [e0, hstep]
    set L := W.lev (a + ((i + 1 : ℕ) : ZMod n)) ζ (W.Q ^ m) with hL
    set F := W.lev (a + (i : ZMod n)) (ζ ^ PD.p) (∏ r ∈ Finset.range i, W.φA^[r] (W.Q ^ m)) with hF
    set φ := φVB PD (LL := LL) (V := T.V) with hφ
    set g0 : ℤ → T.V ⊗[Qp] B := fun k => Lb.levB T a ((ζ ^ PD.p) ^ PD.p ^ i) ⟨x, hN 0 (Nat.zero_le _)⟩ k
      with hg0
    set h : ℤ → T.V ⊗[Qp] B := fun k => ((PD.p : LL) ^ ((i : ℤ) * k)) • φ^[i] (g0 k) with hh
    obtain ⟨m0, hm0⟩ := Lb.supp T a ((ζ ^ PD.p) ^ PD.p ^ i) ⟨x, hN 0 (Nat.zero_le _)⟩
    have hh0 : ∀ k < m0, h k = 0 := fun k hk => by
      simp only [hh, hg0, hm0 k hk, Function.iterate_fixed (map_zero φ) i, smul_zero]
    have hh1 : ∀ k < m0, (fun k => (PD.p : LL) ^ k • φ (h k)) k = 0 := fun k hk => by
      simp only [hh0 k hk, map_zero, smul_zero]
    have hfun : (fun k => (PD.p : LL) ^ k • φ (Lb.levB T (a + (i : ZMod n)) (ζ ^ PD.p)
        ⟨phiIt W T m x i, hNi i le_rfl⟩ k)) = fun k => ConvolutionAlt.cv (PowerSeries.rescale (PD.p : LL) F)
          (fun k => (PD.p : LL) ^ k • φ (h k)) k := by
      funext k'
      rw [ih hNi (ζ ^ PD.p) hζp k']
      exact ConvolutionAlt.cv_twist φ (PD.p : LL) hp0 F h m0 hh0 k'
    show ConvolutionAlt.cv L (fun k => (PD.p : LL) ^ k • φ (Lb.levB T (a + (i : ZMod n)) (ζ ^ PD.p)
        ⟨phiIt W T m x i, hNi i le_rfl⟩ k)) k = _
    rw [hfun, ← ConvolutionAlt.cv_mul L (PowerSeries.rescale (PD.p : LL) F) _ m0 hh1 k]
    have hser : L * PowerSeries.rescale (PD.p : LL) F =
        W.lev (a + ((i + 1 : ℕ) : ZMod n)) ζ (∏ r ∈ Finset.range (i + 1), W.φA^[r] (W.Q ^ m)) := by
      rw [hF, ← hlet, ← lev_φ _ ζ hζ, hL, ← map_mul, Finset.prod_range_succ', map_prod]
      congr 1
      rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [Function.iterate_succ_apply']
    have hfn : (fun k => (PD.p : LL) ^ k • φ (h k)) = fun k => ((PD.p : LL) ^ (((i + 1 : ℕ) : ℤ) * k)) •
        φ^[i + 1] (Lb.levB T a (ζ ^ PD.p ^ (i + 1)) ⟨x, hN 0 (Nat.zero_le _)⟩ k) := by
      funext k'
      simp only [hh, hg0]
      rw [map_smul, smul_smul, ← zpow_add₀ hp0, Function.iterate_succ_apply', ← pow_mul, ← pow_succ']
      congr 2
      push_cast; ring
    rw [hser, hfn]

theorem phiIt_levB (Lb : LevB W) (T : LocLat G Qp LL O)
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (hp0 : (PD.p : LL) ≠ 0)
    (m : ℕ) (c : ZMod n) (ell : ℕ) (x : W.DD T) (hN : ∀ i ≤ ell, phiIt W T m x i ∈ W.N T)
    (s : ℕ) (hs : s < ell) (ζ : LL) (hζ : IsPrimitiveRoot ζ (PD.p ^ (s + 1))) (k : ℤ) :
    Lb.levB T c ζ ⟨phiIt W T m x ell, hN ell le_rfl⟩ k =
      ConvolutionAlt.cv (W.lev c ζ (∏ i ∈ Finset.range ell, W.φA^[i] (W.Q ^ m)))
        (fun k => ((PD.p : LL) ^ ((ell : ℤ) * k)) • (φVB PD (LL := LL) (V := T.V))^[ell]
          (Lb.levB T (c - ell) 1 ⟨x, hN 0 (Nat.zero_le _)⟩ k)) k := by
  have h := phiIt_levB_gen Lb T levB_φ lev_φ hp0 m (c - ell) x ell hN ζ ⟨s + 1, hζ⟩ k
  have h1 : ζ ^ PD.p ^ ell = 1 :=
    (hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow _ hs)
  rw [h1, sub_add_cancel] at h
  exact h

end Formalism.MainNotions.N.Ln03.Pf
end
end
