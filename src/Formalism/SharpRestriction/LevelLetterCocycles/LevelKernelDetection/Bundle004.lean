module

public import Formalism.SharpRestriction.LevelLetterCocycles.ExponentWindowSubsetShort
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.VSumPowNonneg
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

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

section Jumps

variable {T : LocLat G Qp LL O}

theorem pfLvJumps_act (g : G) (z : T.V ⊗[Qp] B) :
    actVdR PD T.ρ g (ιV PD (LL := LL) (V := T.V) z) = ιV PD (LL := LL) (V := T.V) (actVB PD T.ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [actVdR, actVB, ιV, PD.ι_comm]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem pfLvJumps_mul (c : K₀) (z : T.V ⊗[Qp] B) :
    mulVdR (K := K) (BdR := BdR) (V := T.V) (LL := LL) (algebraMap K₀ K c) (ιV PD (LL := LL) (V := T.V) z) =
      ιV PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    simp [mulVdR, mulVB, ιV, map_mul, AlgHom.commutes, IsScalarTower.algebraMap_apply K₀ K BdR]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem pfLvJumps_dcrisL (hK : Function.Surjective (algebraMap K₀ K)) (τ₀ : K₀ →ₐ[Qp] LL)
    (τ : K →ₐ[Qp] LL) (hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = τ₀) (z : T.V ⊗[Qp] B)
    (hz : z ∈ DcrisL PD T.ρ τ₀) : ιV PD (LL := LL) (V := T.V) z ∈ DdRE PD T.ρ τ := by
  rw [DcrisL, Submodule.mem_inf] at hz
  obtain ⟨hz1, hz2⟩ := hz
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz1
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hz2
  rw [DdRE, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro g
    rw [pfLvJumps_act, hz1 g]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro c
    obtain ⟨c', rfl⟩ := hK c
    have hτc : τ (algebraMap K₀ K c') = τ₀ c' := by
      rw [← hτ]
      rfl
    rw [pfLvJumps_mul, hz2 c', map_smul, hτc]

theorem pfLvJumps_fil (hK : Function.Surjective (algebraMap K₀ K)) (τ₀ : K₀ →ₐ[Qp] LL)
    (τ : K →ₐ[Qp] LL) (hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = τ₀) (a : ℤ)
    (h : FildR PD T.ρ τ (a + 1) = FildR PD T.ρ τ a) :
    FilCris PD T.ρ a ⊓ DcrisL PD T.ρ τ₀ = FilCris PD T.ρ (a + 1) ⊓ DcrisL PD T.ρ τ₀ := by
  have key : ∀ b b' : ℤ, FildR PD T.ρ τ b ≤ FildR PD T.ρ τ b' →
      FilCris PD T.ρ b ⊓ DcrisL PD T.ρ τ₀ ≤ FilCris PD T.ρ b' ⊓ DcrisL PD T.ρ τ₀ := by
    intro b b' hbb x hx
    rw [Submodule.mem_inf, FilCris, Submodule.mem_inf, Submodule.mem_comap] at hx
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    have hd : ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ b :=
      (Submodule.mem_inf).2 ⟨pfLvJumps_dcrisL hK τ₀ τ hτ x hx3, hx2⟩
    have hd' := ((Submodule.mem_inf).1 (hbb hd)).2
    exact (Submodule.mem_inf).2 ⟨(Submodule.mem_inf).2 ⟨hx1, hd'⟩, hx3⟩
  exact le_antisymm (key a (a + 1) h.ge) (key (a + 1) a h.le)

theorem pfLvJumps_filD (c : ZMod n) (s : ℕ) (u : ℤ)
    (h : FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (c - (s : ZMod n))) =
      FilCris PD T.ρ (u + 1) ⊓ DcrisL PD T.ρ (W.emb (c - (s : ZMod n)))) :
    FilD W T c s u = FilD W T c s (u + 1) := by
  unfold FilD FilLev
  rw [h]

theorem pfLvJumps_over (hK : Function.Surjective (algebraMap K₀ K)) (τ₀ : K₀ →ₐ[Qp] LL) :
    ∃ τ : K →ₐ[Qp] LL, τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = τ₀ := by
  let e : K₀ ≃ₐ[Qp] K :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) ⟨(algebraMap K₀ K).injective, hK⟩
  refine ⟨τ₀.comp e.symm.toAlgHom, ?_⟩
  ext c
  exact congrArg τ₀ (e.symm_apply_apply c)

theorem pfLvJumps_win (hK : Function.Surjective (algebraMap K₀ K)) (G₀ Sz η : ℕ) (ty : ZMod n → LT)
    (hJ : KindJumps PD T W.emb G₀ Sz η ty) (c : ZMod n) (s : ℕ) (u : ℤ)
    (hu : FilD W T c s u ≠ FilD W T c s (u + 1)) : u ∈ (ty (c - (s : ZMod n))).win G₀ Sz η := by
  obtain ⟨τ, hτ⟩ := pfLvJumps_over hK (W.emb (c - (s : ZMod n)))
  refine hJ (c - (s : ZMod n)) τ hτ u ?_
  intro h
  exact hu (pfLvJumps_filD c s u (pfLvJumps_fil hK _ τ hτ u h))

theorem jumps_holds (hK : Function.Surjective (algebraMap K₀ K)) (c : ZMod n) (ell : ℕ)
    (G₀ Sz η : ℕ) (ty : ZMod n → LT) (hJ : KindJumps PD T W.emb G₀ Sz η ty) :
    ∀ s < ell, Formalism.ExponentWindows.G.Jumps (E.kindAt (kdOf ty) c s) G₀ Sz η (E.sizeAt (bbOf ty) c s) (FilD W T c s) := by
  intro s _
  have hw := pfLvJumps_win hK G₀ Sz η ty hJ c s
  change Formalism.ExponentWindows.G.Jumps (kdOf ty (c - (s : ZMod n))) G₀ Sz η (bbOf ty (c - (s : ZMod n))) (FilD W T c s)
  cases h : ty (c - (s : ZMod n)) with
  | thin =>
    simp only [kdOf, h, Formalism.ExponentWindows.G.Jumps]
    intro u hu
    simpa [LT.win, h] using hw u hu
  | up b =>
    simp only [kdOf, bbOf, h, LT.size, Formalism.ExponentWindows.G.Jumps]
    intro u hu
    simpa [LT.win, h] using hw u hu
  | down b =>
    simp only [kdOf, bbOf, h, LT.size, Formalism.ExponentWindows.G.Jumps]
    intro u hu
    simpa [LT.win, h] using hw u hu

theorem jumps_holds_quot (hK : Function.Surjective (algebraMap K₀ K))
    (hQuot : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hc₁ : CrysLat PD T₁) (hc₂ : CrysLat PD T₂)
    (hon : F.Onto) (c : ZMod n) (ell : ℕ) (G₀ Sz η : ℕ) (ty : ZMod n → LT)
    (hJ : KindJumps PD T₁ W.emb G₀ Sz η ty) :
    ∀ s < ell, Formalism.ExponentWindows.G.Jumps (E.kindAt (kdOf ty) c s) G₀ Sz η (E.sizeAt (bbOf ty) c s)
      (FilD W T₂ c s) :=
  jumps_holds hK c ell G₀ Sz η ty fun i τ hτ a ha => hJ i τ hτ a (hQuot T₁ T₂ F hc₁ hc₂ hon τ a ha)

end Jumps

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03
open Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W}

theorem crystalline_to_deRham_injective (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem levelExpansion_smul
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T)) (k : ℤ) :
    Lb.levB T i ζ (a • x) k = cv (W.lev i ζ a) (Lb.levB T i ζ x) k := by
  obtain ⟨m, hm⟩ := Lb.supp T i ζ x
  apply crystalline_to_deRham_injective (PD := PD) (LL := LL) T
  rw [← levN_eq, W.levN_smul, cv_map _ _ _ m hm]
  unfold cv
  congr 1
  funext j
  rw [levN_eq]

theorem level_pi_constantCoeff_zero (i : ZMod n) :
    PowerSeries.constantCoeff (W.lev i 1 (letπ : LetA O n)) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 ⟨0, by simp⟩
  have h := congrArg PowerSeries.constantCoeff hE
  simp only [map_add (f := _), map_mul, hE0, mul_one, map_one] at h
  linear_combination h

theorem levelExpansion_neg_eq_zero
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (T : LocLat G Qp LL O)
    (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) (i : ZMod n) (x : ↥(W.N T)) (k : ℤ) (hk : k < 0) :
    Lb.levB T i 1 x k = 0 := by
  have hX : PowerSeries.constantCoeff (W.lev i 1 W.X) = 0 := by
    have : W.X = (letπ : LetA O n) := by
      show (W.φA ^ (W.s - 1)) _ = _
      rw [hs1, Nat.sub_self, pow_zero]
      rfl
    rw [this]
    exact level_pi_constantCoeff_zero (W := W) i
  apply crystalline_to_deRham_injective (PD := PD) (LL := LL) T
  rw [← levN_eq, map_zero]
  exact ((hP4.1 i 1 ⟨0, by simp⟩ hX).1 x k).2 hk

theorem level_pi0_X_pow_dvd
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (i : ZMod n) : (PowerSeries.X : PowerSeries LL) ^ (PD.p - 1) ∣ W.lev i 1 W.π₀ := by
  obtain ⟨w, hw⟩ := hp9.2.2.1
  rw [hw, map_mul, map_pow]
  refine Dvd.dvd.mul_left (pow_dvd_pow_of_dvd ?_ _) _
  rw [PowerSeries.X_dvd_iff]
  exact level_pi_constantCoeff_zero (W := W) i

theorem levelExpansion_gamma
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (x : ↥(W.N T))
    (hx : W.γD T W.gam (x : W.DD T) ∈ W.N T) (k : ℤ) :
    Lb.levB T i 1 ⟨W.γD T W.gam (x : W.DD T), hx⟩ k =
      (algebraMap O LL (W.χΓ W.gam : O)) ^ k • Lb.levB T i 1 x k := by
  refine levB_Γ T hT W.gam i 1 1 0 1 (by simp) ?_ (by simp) x hx k
  rw [Nat.cast_one, W.gam_gen]
  simp

theorem expansion_at_one
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hs1 : W.s = 1) (hp2 : PD.p ≠ 2) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (i : ZMod n) (x y : ↥(W.N T)) (M : ℕ) (hx : W.γD T W.gam (x : W.DD T) ∈ W.N T)
    (hxy : W.γD T W.gam (x : W.DD T) - (x : W.DD T) = W.π₀ ^ M • (y : W.DD T))
    (k : ℤ) (hk0 : 0 < k) (hk : k < (((PD.p - 1) * M : ℕ) : ℤ)) : Lb.levB T i 1 x k = 0 := by
  have hsub : (⟨W.γD T W.gam (x : W.DD T), hx⟩ : ↥(W.N T)) - x = W.π₀ ^ M • y := Subtype.ext (by
    rw [Submodule.coe_sub, Submodule.coe_smul]
    exact hxy)
  have hz : Lb.levB T i 1 (W.π₀ ^ M • y) k = 0 := by
    rw [levelExpansion_smul levN_eq]
    refine cv_vanish _ _ (fun k hk => levelExpansion_neg_eq_zero levN_eq hs1 T hP4 i y k hk) ((PD.p - 1) * M) ?_ k hk
    rw [map_pow, pow_mul]
    exact pow_dvd_pow_of_dvd (level_pi0_X_pow_dvd hp9 i) M
  have he : Lb.levB T i 1 ⟨W.γD T W.gam (x : W.DD T), hx⟩ k - Lb.levB T i 1 x k = 0 := by
    rw [← Pi.sub_apply, ← map_sub, hsub]
    exact hz
  rw [levelExpansion_gamma levB_Γ T hT i x hx k] at he
  have he' : ((algebraMap O LL (W.χΓ W.gam : O)) ^ k - 1) • Lb.levB T i 1 x k = 0 := by
    rw [sub_smul, one_smul]
    exact he
  have hu : (algebraMap O LL (W.χΓ W.gam : O)) ^ k ≠ 1 := by
    refine ValuationPow.zpow_ne_one v PD.p PD.hp hp2 W.v_l _ ?_ k hk0.ne'
    rw [W.gam_gen, hs1]
    simp
  exact (smul_eq_zero.1 he').resolve_left (sub_ne_zero.2 hu)

end Formalism.MainNotions.N.Ln03.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

theorem inverse_unit_mul_X_pow {Ks : Type} [CommRing Ks] (w : (PowerSeries Ks)ˣ) (m : ℕ) :
    Ring.inverse (HahnSeries.ofPowerSeries ℤ Ks ((w : PowerSeries Ks) * PowerSeries.X ^ m)) =
      HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) * tp Ks (-(m : ℤ)) := by
  have h1 : HahnSeries.ofPowerSeries ℤ Ks (↑w : PowerSeries Ks) *
      HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have ht : tp Ks (m : ℤ) * tp Ks (-(m : ℤ)) = 1 := by
    rw [tp, tp, HahnSeries.single_mul_single, add_neg_cancel, mul_one]
    rfl
  let U : (HahnSeries ℤ Ks)ˣ :=
    { val := HahnSeries.ofPowerSeries ℤ Ks (↑w : PowerSeries Ks) * tp Ks (m : ℤ)
      inv := HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) * tp Ks (-(m : ℤ))
      val_inv := by linear_combination (tp Ks (m : ℤ) * tp Ks (-(m : ℤ))) * h1 + ht
      inv_val := by linear_combination (tp Ks (m : ℤ) * tp Ks (-(m : ℤ))) * h1 + ht }
  have hU : HahnSeries.ofPowerSeries ℤ Ks ((w : PowerSeries Ks) * PowerSeries.X ^ m) = ↑U := by
    rw [map_mul, HahnSeries.ofPowerSeries_X_pow]
    rfl
  rw [hU, Ring.inverse_unit]
  rfl

theorem evaluation_comm_tensor {LL D ι : Type} [Field LL] [AddCommGroup D] [Module LL D] [Fintype ι]
    [DecidableEq ι] (i : ι) (z : D ⊗[LL] (ι → LL)) :
    evK i (TensorProduct.comm LL D (ι → LL) z) = TensorProduct.piScalarRight LL LL D ι z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul d f =>
    rw [TensorProduct.comm_tmul, evaluation_tmul, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), hz, hz', map_add (f := _), Pi.add_apply]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}


open Classical in
theorem evaluation_expansion_at_root (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (g : Rs LL PD.p s → D) (ζ : Rs LL PD.p s) : evK ζ (toKsD W s D g) = g ζ := by
  rw [toKsD, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, evaluation_comm_tensor,
    LinearEquiv.apply_symm_apply]

theorem rho_product_unit_mul {ell : ℕ}
    (hk1b : ∀ s < ell, ∃ ε : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X)
    (hunits : ∀ s < ell, IsUnit (rhoL hR c s PowerSeries.X) ∧
      ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')))
    (E : ℕ → ℕ) (s : ℕ) (hs : s < ell) :
    ∃ w : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ E s') =
        (w : PowerSeries (KsW W s)) * PowerSeries.X ^ E s := by
  obtain ⟨ε, hε⟩ := hk1b s hs
  have hrest : IsUnit (rhoL hR c s
      (∏ s' ∈ (Finset.range ell).erase s, (baseIdOf hR).Bs.p s' ^ E s')) := by
    rw [map_prod]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun s' hs' => ?_
    rw [map_pow]
    obtain ⟨hne, hlt⟩ := Finset.mem_erase.1 hs'
    exact ((hunits s hs).2 s' (Finset.mem_range.1 hlt) hne).pow _
  obtain ⟨u, hu⟩ := hrest
  refine ⟨ε ^ E s * u, ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), map_mul, ← hu, map_pow, hε]
  push_cast
  ring


open Classical in
theorem levelCond_iff (ell : ℕ)
    (hk1b : ∀ s < ell, ∃ ε : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X)
    (hunits : ∀ s < ell, IsUnit (rhoL hR c s PowerSeries.X) ∧
      ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')))
    (E : ℕ → ℕ) (s : ℕ) (hs : s < ell) (x : C.V) (hx : x ∈ (latOf C).N c)
    (hFil : ∀ s, Antitone (FilD W T c s)) :
    Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s)
        (rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ E s'))) •
      expN Lb s T c ⟨C.t c x, hx⟩ ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) ↔
    ∀ (ζ : Rs LL PD.p s) (k : ℤ),
      (⟨Lb.levB T c ζ ⟨C.t c x, hx⟩ k, Lb.mem T c ζ ⟨C.t c x, hx⟩ k⟩ : Dc W T c) ∈
        FilD W T c s ((E s : ℤ) - k) := by
  obtain ⟨w, hw⟩ := rho_product_unit_mul hk1b hunits E s hs
  have hX : Monotone fun i : ℤ => FilD W T c s (-i) := fun i j hij => hFil s (neg_le_neg hij)
  rw [hw, inverse_unit_mul_X_pow, xi_unit_tp _ hX _ _ (Units.inv_mul w), xi_iff]
  refine forall_congr' fun ζ => forall_congr' fun k => ?_
  have hc : cf (expN Lb s T c ⟨C.t c x, hx⟩) k = coefN Lb s T c ⟨C.t c x, hx⟩ k := rfl
  rw [hc, coefN, evaluation_expansion_at_root, show -(k + -(E s : ℤ)) = (E s : ℤ) - k by ring]

end Formalism.MainNotions.N.Ln03.K8
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {W : LocWach PD LL O v n}

theorem Pf_HOmega_pow_card (δ : W.Gam) (hδ : δ ∈ W.DelF) : δ ^ W.DelF.card = 1 := by
  have hH : ∀ g : W.Gam, g ∈ CommGroup.torsion W.Gam ↔ g ∈ W.DelF := by
    intro g
    rw [W.DelF_def, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  have hset : ((CommGroup.torsion W.Gam : Subgroup W.Gam) : Set W.Gam) = (W.DelF : Set W.Gam) := by
    ext g
    simp only [SetLike.mem_coe]
    exact hH g
  have hcardH : Nat.card (CommGroup.torsion W.Gam) = W.DelF.card := by
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hd := orderOf_dvd_natCard (⟨δ, (hH δ).2 hδ⟩ : CommGroup.torsion W.Gam)
  rw [Subgroup.orderOf_mk, hcardH] at hd
  exact orderOf_dvd_iff_pow_eq_one.1 hd

theorem hω_holds (hcard : W.DelF.card = PD.p - 1) (hinj : Function.Injective (algebraMap O LL))
    (ιZ : ℤ_[PD.p] →+* O) :
    ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF, algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ω.1) := by
  classical
  intro ω
  have hpos : 0 < PD.p - 1 := by have := PD.hp.two_le; omega
  set f : W.Gam → LL := fun g => algebraMap O LL (W.χΓ g : O) with hf
  have hAcard : (W.DelF.image f).card = PD.p - 1 := by
    rw [Finset.card_image_of_injOn, hcard]
    intro x _ y _ hxy
    apply W.χΓ_inj
    apply Units.ext
    exact hinj hxy
  have hARt : W.DelF.image f ⊆ Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    rw [Polynomial.mem_nthRootsFinset hpos]
    have h1 : g ^ (PD.p - 1) = 1 := hcard ▸ Pf_HOmega_pow_card g hg
    simp only [hf]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one, map_one]
  have hRt : (Polynomial.nthRootsFinset (PD.p - 1) (1 : LL)).card ≤ PD.p - 1 := by
    unfold Polynomial.nthRootsFinset
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  have hEq : W.DelF.image f = Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) :=
    Finset.eq_of_subset_of_card_le hARt (by omega)
  have hωR : algebraMap O LL (ιZ ω.1) ∈ Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) := by
    rw [Polynomial.mem_nthRootsFinset hpos, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ω.2,
      Units.val_one, map_one, map_one]
  rw [← hEq] at hωR
  obtain ⟨g, hg, hgω⟩ := Finset.mem_image.1 hωR
  exact ⟨g, hg, hgω⟩

end Formalism.MainNotions.N.Ln03.Pf
end
end
