module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantLetterIdempotentOfFixed
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle024
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle025
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfAssemble
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle031
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle028
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle035
public import Formalism.SharpRestriction.LevelLetterCocycles.FrameInvPoly
import Formalism.SharpRestriction.LevelLetterCocycles.HorTrUnique
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle034
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle032
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle033
public import Formalism.SharpRestriction.LevelLetterCocycles.KillWinLOf
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

@[expose] public section

section

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2T

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX TCase)
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem basis_induction {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] (b : Module.Basis ι R M)
    (P : M → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (a : R) x, P x → P (a • x)) (hb : ∀ k, P (b k)) : ∀ x, P x := by
  intro x
  have hx : x ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hb k
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | smul a y _ hy => exact hsmul a y hy

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem exists_linear_lift_of_free [NeZero n] [IsDomain O] [IsPrincipalIdealRing O] (hZ : TTool2Z W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hp : 11 ≤ PD.p) {M η σ : ℕ} (hTC : TCase PD.p 1 M η σ)
    (hc : IsCrys PD T.ρ) (c : ZMod n) {FF : Type} [AddCommGroup FF] [Module O FF]
    [Module.Free O FF] [Module.Finite O FF] (F₁ : Submodule O FF) (ζL : FF →ₗ[O] W.DD T)
    (hζ : ∀ f, DL W T c (ζL f) ∧ InPN W T 1 (ζL f)) :
    ∃ tL : ↥F₁ →ₗ[O] W.DD T, ∀ f : ↥F₁, tL f ∈ pullJ W T c 1 ∧ DL W T (c + 1) (tL f) ∧
      (∃ p ∈ pullJ W T c 1, ((PD.p : ℕ) : O) ^ σ • W.φD T (ζL f) - (W.γ T (tL f) - tL f) =
        fMX W M η • p) ∧
      ∃ t', IsTrZ W T c 1 M η σ (ζL f) t' ∧ ∃ p ∈ pullJ W T c 1, tL f - t' = fMX W M η • p := by
  obtain ⟨Zex, Zpr, Zlin, -⟩ := hZ hA hp 1 M η σ hTC T hc c
  simp only [pow_one, Nat.cast_one] at Zpr
  let bF := Module.Free.chooseBasis O FF
  obtain ⟨r, b1⟩ := Submodule.basisOfPid bF F₁
  let tch : FF → W.DD T := fun f => Classical.epsilon (fun t => IsTrZ W T c 1 M η σ (ζL f) t)
  have htch : ∀ f, IsTrZ W T c 1 M η σ (ζL f) (tch f) := fun f =>
    Classical.epsilon_spec (Zex _ (hζ f).1 (hζ f).2)
  let tL : ↥F₁ →ₗ[O] W.DD T := b1.constr O (fun k => tch (b1 k : FF))
  refine ⟨tL, ?_⟩

  have hz0 : ∀ t, IsTrZ W T c 1 M η σ 0 t → ∃ p ∈ pullJ W T c 1, t = fMX W M η • p := by
    intro t ht
    have hd0 := invariantLetter_zero W T c
    have hp0 := uniformizerLattice_zero W T (k := 1)
    obtain ⟨p, hp, e⟩ := Zlin 0 0 0 0 t t t hd0 hp0 hd0 hp0 ht ht (by simpa using ht)
    exact ⟨p, hp, by simpa using e⟩
  refine basis_induction b1 _ ?_ ?_ ?_ ?_
  · obtain ⟨t0, ht0⟩ := Zex 0 (invariantLetter_zero W T c) (uniformizerLattice_zero W T 1)
    obtain ⟨p0, hp0, e0⟩ := hz0 t0 (by simpa using ht0)
    refine ⟨by simp, by simpa using invariantLetter_zero W T (c + 1), ⟨0, Submodule.zero_mem _, by simp⟩,
      t0, by simpa using ht0, -p0, Submodule.neg_mem _ hp0, ?_⟩
    simp [e0]
  · rintro x y ⟨hx1, hx2, ⟨px, hpx, ex⟩, tx, htx, qx, hqx, fx⟩ ⟨hy1, hy2, ⟨py, hpy, ey⟩, ty, hty, qy, hqy, fy⟩
    have hsum : ζL (x : FF) + ζL (y : FF) = ζL ((x + y : ↥F₁) : FF) := by
      rw [Submodule.coe_add, map_add (f := _)]
    obtain ⟨txy, htxy⟩ := Zex (ζL ((x + y : ↥F₁) : FF)) (hζ _).1 (hζ _).2
    obtain ⟨r1, hr1, e1⟩ := Zlin 1 1 _ _ tx ty txy (hζ x).1 (hζ x).2 (hζ y).1 (hζ y).2 htx hty
      (by rw [one_smul, one_smul, hsum]; exact htxy)
    refine ⟨by rw [map_add (f := _)]; exact Submodule.add_mem _ hx1 hy1,
      by rw [map_add (f := _)]; exact Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T hx2 hy2,
      ⟨px + py, Submodule.add_mem _ hpx hpy, ?_⟩, txy, htxy, qx + qy - r1,
      Submodule.sub_mem _ (Submodule.add_mem _ hqx hqy) hr1, ?_⟩
    · rw [smul_add, ← ex, ← ey, Submodule.coe_add, map_add ζL, map_add (W.φD T), smul_add,
        map_add tL, map_add (W.γ T)]
      abel
    · rw [smul_sub, smul_add, ← fx, ← fy, ← e1, map_add tL, one_smul, one_smul]
      abel
  · rintro a x ⟨hx1, hx2, ⟨px, hpx, ex⟩, tx, htx, qx, hqx, fx⟩
    have hsm : a • ζL (x : FF) = ζL ((a • x : ↥F₁) : FF) := by
      rw [Submodule.coe_smul, map_smul]
    obtain ⟨tax, htax⟩ := Zex (ζL ((a • x : ↥F₁) : FF)) (hζ _).1 (hζ _).2
    obtain ⟨r1, hr1, e1⟩ := Zlin a 0 _ _ tx tx tax (hζ x).1 (hζ x).2 (hζ x).1 (hζ x).2 htx htx
      (by rw [zero_smul, add_zero, hsm]; exact htax)
    refine ⟨by rw [map_smul]; exact Submodule.smul_of_tower_mem _ a hx1,
      by rw [map_smul]; exact Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T a hx2,
      ⟨a • px, Submodule.smul_of_tower_mem _ a hpx, ?_⟩, tax, htax, a • qx - r1,
      Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ a hqx) hr1, ?_⟩
    · rw [smul_comm (fMX W M η) a px, ← ex]
      simp only [map_smul, Submodule.coe_smul, smul_sub]
      rw [smul_comm]
    · rw [smul_sub, smul_comm (fMX W M η) a qx, ← fx, ← e1]
      simp only [map_smul, zero_smul, add_zero, smul_sub]
      abel
  · intro k
    have hk : tL (b1 k) = tch (b1 k : FF) := by simp [tL]
    obtain ⟨h1, h2, h3⟩ := Zpr _ _ (hζ _).1 (hζ _).2 (htch (b1 k : FF))
    refine ⟨by rw [hk]; exact h2, by rw [hk]; exact h1, by rw [hk]; exact h3, tch (b1 k : FF),
      htch _, 0, Submodule.zero_mem _, by rw [hk, sub_self, smul_zero]⟩

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2T

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows IsLocalRing

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem basis_of {I : BaseId W} {T : LocLat G Qp LL O} (hInj : I.Inj) (hFull : I.Full)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (C : Coord W I T) (i : ZMod n) :
    ∃ (r : ℕ) (e : Fin r → C.V) (b : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N i)),
      ∀ k, (b k : C.V) = e k := by
  obtain ⟨r, e, hli, hsp⟩ := free_of hInj hFull hmod C i
  refine ⟨r, e, (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp), fun k => ?_⟩
  simp [Module.Basis.span_apply]

theorem matrix_of {V₁ V₂ : Type} [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
    [Module (PowerSeries O) V₂] {N₂ : Submodule (PowerSeries O) V₂} {r₁ r₂ : ℕ} (f : V₁ → V₂)
    (e₁ : Fin r₁ → V₁) (e₂ : Fin r₂ → V₂) (b₂ : Module.Basis (Fin r₂) (PowerSeries O) ↥N₂)
    (hb₂ : ∀ k, (b₂ k : V₂) = e₂ k) (hf : ∀ k, f (e₁ k) ∈ N₂) :
    ∃ P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O), ∀ k, ∃ a : Fin r₂ → PowerSeries O,
      f (e₁ k) = ∑ l, a l • e₂ l ∧ ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l) := by
  refine ⟨Matrix.toLin' (Matrix.of fun l k => PowerSeries.constantCoeff (b₂.repr ⟨_, hf k⟩ l)),
    fun k => ⟨fun l => b₂.repr ⟨_, hf k⟩ l, ?_, fun l => by simp⟩⟩
  have h := b₂.sum_repr ⟨_, hf k⟩
  have h' := congrArg (fun x : ↥N₂ => (x : V₂)) h
  simp only [Submodule.coe_sum, Submodule.coe_smul, hb₂] at h'
  exact h'.symm

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero LL]
  [IsFractionRing O LL] [Fintype (K →ₐ[Qp] LL)]

theorem realised2_pf (Lb : LevB W) (hR : Ring9 W) (e : W.DD W.one) (uZ : ℤ_[PD.p]ˣ)
    (ιZ : ℤ_[PD.p] →+* O)
    (hLevN : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hCmp : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (x : ↥(W.N T)),
      W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)
    (hLevBφ : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL),
      (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) • φVB PD (LL := LL) (V := T.V)
            (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (hLevBΓ : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL)
      (j a : ℕ), IsPrimitiveRoot ζ (PD.p ^ j) →
      (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) → ζ' = ζ ^ a →
      ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hLevΓ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ), IsPrimitiveRoot ζ (PD.p ^ j) →
      (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) → ζ' = ζ ^ a →
      ∀ f : LetA O n, W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (hLevφ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (hs : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hP4Lev : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W) (hDdR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL)
    (hHod : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ →
      F.Onto → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    (hV : ValRing O v) (hK : Function.Bijective (algebraMap K₀ K))
    (hpm : (PD.p : O) ∈ maximalIdeal O) (hrich : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (huZ : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (he : UnitGen W e) (hone : IsCrys PD W.one.ρ) (h5 : 5 ≤ PD.p) : Realised2 hR e := by
  intro T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen hCu hKJ hJ hg hS hT
  obtain ⟨C₁, C₂, C₀, hC, e₀, he₀⟩ :=
    Formalism.MainNotions.N.Ln03.Pf.coordSteps_holds hR hs hP9 hLem3 hDdR he hone hK h5 T₁ T₂ F hc₁ hc₂ hon
  refine ⟨{ C₁ := C₁, C₂ := C₂, C₀ := C₀, h := hC, e₀ := e₀, Ks := KsW W, Δ := DeltaT PD.p },
    { he₀ := he₀, arcs := fun ϖ hϖ c hc => ?_ }⟩
  have hp2 : PD.p ≠ 2 := by omega
  have hp9 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀ := fun T hT =>
    ((hP9 T hT hs hp2).2.2 (unram_of hK)).2
  obtain ⟨r₁, e₁, b₁, hb₁⟩ := basis_of (baseIdOf_inj hR) (baseIdOf_full hR) (hp9 T₁ hc₁.2.2.2) C₁
    (c - ((cutsOf hCu).ell c : ZMod n))
  obtain ⟨r₂, e₂, b₂, hb₂⟩ := basis_of (baseIdOf_inj hR) (baseIdOf_full hR) (hp9 T₂ hc₂.2.2.2) C₂
    (c - ((cutsOf hCu).ell c : ZMod n))
  obtain ⟨P, hP⟩ := matrix_of (latHomOf hC).f e₁ e₂ b₂ hb₂ (fun k =>
    (latHomOf hC).map_N _ _ (by rw [← hb₁ k]; exact (b₁ k).2))
  exact Formalism.MainNotions.N.Ln03.Pf.finalArc_holds Lb uZ ιZ hC c _ _ ϖ j _ _ Gp S η ty e₁ e₂ P hLevN hCmp hLevBφ
    hLevBΓ hLevΓ hLevφ hs hP4 hP4Lev hSat hP3 hP9 hP5 hDdR hHod hc₁ hc₂ hon hKJ hV hK hϖ hpm
    (Formalism.MainNotions.N.Ln03.Pf.hn_of hCu hc) hrich (glue2 hR) (cyclotomicFrobeniusPowerSeries_X W)
    (fun s _ ζ hζ => rhoZ_exp c ζ ⟨s + 1, (mem_primitiveRoots (pow_pos PD.hp.pos _)).1 hζ⟩)
    huZ hutie (Formalism.MainNotions.N.Ln03.Pf.teichOnto_holds PD.p) h5 b₁ hb₁ b₂ hb₂ hP
    (Formalism.MainNotions.N.Ln03.Pf.hj_of hCu hc) (Formalism.MainNotions.N.Ln03.Pf.three_g_le_parameter_bound PD.hp.two_le hg)

end Formalism.MainNotions.N.Ln03
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

def Good (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (z : W.DD T) : Prop :=
  InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z) ∧
  ∀ (k : ℕ) (f : Fin d → W.EE),
    RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k • z) f →
    (∀ m, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f m)) →
    ∃ κ : ℕ, SecIn W (c' + (e : ZMod n)) e (condNN W T (c' + (e : ZMod n)) e b) fun m => lE W κ * f m

theorem lE_mul (s t : ℕ) (y : W.EE) : lE W s * (lE W t * y) = lE W (s + t) * y := by
  unfold lE; rw [pow_add]; ring

theorem lE_eq (t : ℕ) : lE W t = algebraMap (LetA O n) W.EE (lA W ^ t) := by
  unfold lE lA; rw [map_pow, map_natCast]

theorem repVV_lA (T : LocLat G Qp LL O) (c' : ZMod n) (e M : ℕ) (Λ : LetA O n) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (z : W.DD T) (f : Fin d → W.EE) (s t : ℕ)
    (h : RepVV W T c' e M Λ b sol (lA W ^ t • z) f) :
    RepVV W T c' e M Λ b sol (lA W ^ (t + s) • z) (fun m => lE W s * f m) := by
  have := repVV_smul W T c' e M Λ b sol _ f (lA_mem W s) h
  rwa [lA_smul_smul, ← lE_eq] at this

theorem good_of_sec (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (z : W.DD T)
    (hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z)) (k₀ : ℕ) (f₀ : Fin d → W.EE)
    (hrep₀ : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k₀ • z) f₀)
    (hfr₀ : ∀ m, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f₀ m)) (κ₀ : ℕ)
    (hS₀ : SecIn W (c' + (e : ZMod n)) e (condNN W T (c' + (e : ZMod n)) e b) fun m => lE W κ₀ * f₀ m) :
    Good A c' e T b sol z := by
  refine ⟨hz, fun k f hrep hfr => ?_⟩
  have r1 := repVV_lA T c' e _ _ b sol z f k₀ k hrep
  have r2 := repVV_lA T c' e _ _ b sol z f₀ k k₀ hrep₀
  rw [add_comm k₀ k] at r2
  obtain ⟨t, ht⟩ := sec_unique W C.hinj C.hV C.hO2 C.hs C.hR C.hp0 C.h5 C.hTr C.hH C.hCA C.h5p T
    (C.h3 T hT.1) (C.hmod T hT.1) A hA c' hc' hT b sol hb e _ _ _ r1 r2
    (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr m) k₀) (fun m => Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₀ m) k)
  have hD := secIn_piLam W C.hR.1 A (c' + (e : ZMod n)) e T b
    (fun c₀ s hs => dvO_filLow W C.hbij A hA c' hc' T hT b hb.1 e s hs c₀) _ ht
  have hS := secIn_add W (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hD κ₀) (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₀ (t + k))
  refine ⟨κ₀ + (t + k₀), ?_⟩
  convert hS using 1
  rw [show κ₀ + (t + k₀) = κ₀ + (t + k₀) from rfl]
  unfold lE
  funext m
  simp only [Pi.add_apply]
  ring

theorem good_of_lpow (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e K : ℕ) (z : W.DD T)
    (hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z)) (h : Good A c' e T b sol (lA W ^ K • z)) :
    Good A c' e T b sol z := by
  obtain ⟨κ, f, hrep, hfr⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol hb _
    h.1
  obtain ⟨κ', hS⟩ := h.2 κ f hrep hfr
  rw [lA_smul_smul] at hrep
  exact good_of_sec C A hA c' hc' T hT b sol hb e z hz _ f hrep hfr κ' hS

theorem good_add (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (z₁ z₂ : W.DD T)
    (h₁ : Good A c' e T b sol z₁) (h₂ : Good A c' e T b sol z₂) : Good A c' e T b sol (z₁ + z₂) := by
  have hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (z₁ + z₂)) := by
    rw [smul_add]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c' e _ h₁.1 h₂.1
  obtain ⟨κ₁, f₁, hrep₁, hfr₁⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol
    hb _ h₁.1
  obtain ⟨κ₂, f₂, hrep₂, hfr₂⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1 b sol
    hb _ h₂.1
  obtain ⟨κ'₁, hS₁⟩ := h₁.2 κ₁ f₁ hrep₁ hfr₁
  obtain ⟨κ'₂, hS₂⟩ := h₂.2 κ₂ f₂ hrep₂ hfr₂
  have r1 := repVV_lA T c' e _ _ b sol z₁ f₁ κ₂ κ₁ hrep₁
  have r2 := repVV_lA T c' e _ _ b sol z₂ f₂ κ₁ κ₂ hrep₂
  rw [add_comm κ₂ κ₁] at r2
  have r := repVV_add W C.hinj T c' e _ _ b sol _ _ _ _ r1 r2
  rw [← smul_add] at r
  refine good_of_sec C A hA c' hc' T hT b sol hb e _ hz _ _ r
    (fun m => inFr_add W (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₁ m) κ₂) (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfr₂ m) κ₁))
    (κ'₁ + κ'₂) ?_
  have hS := secIn_add W (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₁ (κ'₂ + κ₂))
    (Formalism.MainNotions.UnusedSlot80.ArcF.secIn_lE W hS₂ (κ'₁ + κ₁))
  convert hS using 1
  unfold lE
  funext m
  simp only [Pi.add_apply]
  ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem universal_general_of_inverse_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (h15 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D)
    (hInv : AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG))
    (hUG : UnivGenL D HW) : UniversalComponentCaseA D HW F Cm :=
  universal_general_of_window D HW F Cm hAdm h9 hH h15 (killWinL_of D HW F Cm hAdm h9 hInv) hUG

end Formalism.MainNotions.UnusedSlot80
end
end

section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Parts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure LevBasics (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) where
  F : Type
  fF : Field F
  algOF : Algebra O F
  inj : Function.Injective (algebraMap O F)
  hp : ((PD.p : ℕ) : F) ≠ 0
  root : ∃ ζ : F, IsPrimitiveRoot ζ (PD.p ^ (s + 1))
  ev : Rs F PD.p s → LetA O n →+* F
  ev_O : ∀ (ζ : Rs F PD.p s) (x : O), ev ζ (algebraMap O (LetA O n) x) = algebraMap O F x
  ev_letE : ∀ ζ : Rs F PD.p s, ev ζ (letE a) = 1
  ev_π : ∀ ζ : Rs F PD.p s, ev ζ letπ = (ζ : F) - 1
  ev_ps : ∀ ζ : Rs F PD.p s, ev ζ (ps W s) = 0
  ev_pt : ∀ t, t ≠ s → ∀ ζ : Rs F PD.p s, ev ζ (ps W t) ≠ 0
  σ : W.Gam → (ZMod (PD.p ^ (s + 1)))ˣ
  ev_γ : ∀ g (ζ : Rs F PD.p s) x, ev ζ (W.γA g x) = ev (powR F PD.p s (σ g) ζ) x
  gen : Subgroup.closure (insert (σ W.gam) (σ '' (W.DelF : Set W.Gam))) = ⊤

attribute [instance] LevBasics.fF LevBasics.algOF

def LevDiv (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) (F : Type) [Field F] [Algebra O F]
    (ev : Rs F PD.p s → LetA O n →+* F) : Prop :=
  ∀ g ∈ W.AΔ, (∀ ζ : Rs F PD.p s, ev ζ g = 0) → ∃ (κ : ℕ) (w : LetA O n), w ∈ W.AΔ ∧
    ((PD.p : ℕ) : LetA O n) ^ κ * (letE a * g) = ps W s * w

def LevRat (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) (F : Type) [Field F] [Algebra O F]
    (ev : Rs F PD.p s → LetA O n →+* F) : Prop :=
  ∀ g ∈ W.AΔ, ∀ d ∈ W.AΔ, (∀ ζ : Rs F PD.p s, ev ζ d ≠ 0) → ∀ c : F,
    (∀ ζ : Rs F PD.p s, ev ζ g = c * ev ζ d) →
    ∃ (κ : ℕ) (x : O), ((PD.p : ℕ) : F) ^ κ * c = algebraMap O F x

def levEv_of (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) (hB : LevBasics W a s) (hD : LevDiv W a s hB.F hB.ev)
    (hR : LevRat W a s hB.F hB.ev) : LevEv W a s where
  F := hB.F
  fF := hB.fF
  algOF := hB.algOF
  hp := hB.hp
  ev := hB.ev
  ev_O := hB.ev_O
  ev_letE := hB.ev_letE
  ev_ps := hB.ev_ps
  ev_pt := hB.ev_pt
  σ := hB.σ
  ev_γ := hB.ev_γ
  gen := hB.gen
  div := hD
  rat := hR

theorem invLevCore_of_parts (W : LocWach PD LL O v n) (hπ : W.π₀ ∈ W.AΔ) (hB : ∀ a s, LevBasics W a s)
    (hD : ∀ a s, LevDiv W a s (hB a s).F (hB a s).ev) (hR : ∀ a s, LevRat W a s (hB a s).F (hB a s).ev)
    (hPC : InvCut.PrecompConst) : CutU.InvLevCore W :=
  invLevCore_of W hπ (fun a s => levEv_of W a s (hB a s) (hD a s) (hR a s)) hPC

end Parts

end Formalism.MainNotions.UnusedSlot80.InvW
end
end
