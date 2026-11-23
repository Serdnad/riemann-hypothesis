module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle182
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle186
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMoveProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuadricCharacterLeakSharesFinite
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusModulusUnipotentRadicalUnitaryGroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
import Formalism.HarderNarasimhan.ShiftInvariance
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.lebesgueCommonStabilizer_eq_radical_levi_map : ∀ (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → lebR0 k r j β = (volume : Measure ((UTin β → ℂ) × PTop k r j)).map (fun q => Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1))) ∧ Set.range (rEl k r j β) = Set.range (fun q : (UTin β → ℂ) × PTop k r j => pTop k r j q.2 * uEmb k r (upperIn β q.1)) ∧ Function.Injective (fun q : (UTin β → ℂ) × PTop k r j => pTop k r j q.2 * uEmb k r (upperIn β q.1)) ∧ (j = 0 → lebR0 k r j β = lebN k r) := by
  first | exact @GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product | exact GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product | (intros; apply GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LoopC.Centre

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def nil (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) : S.V →ₗ[E] S.V :=
  ∑ a, ∑ a', (c a a' • S.hT (e a')).smulRight (e a)

theorem nil_apply (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) (x : S.V) :
    nil e c x = ∑ a, ∑ a', (c a a' * S.hT (e a') x) • e a := by
  simp [nil]

theorem nil_eq_zero (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) (x : S.V)
    (hx : ∀ a, S.hT (e a) x = 0) : nil e c x = 0 := by
  rw [nil_apply]
  simp [hx]

theorem hT_nil (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (x : S.V) (a : Fin r) : S.hT (e a) (nil e c x) = 0 := by

  rw [nil_apply, map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_

  rw [map_sum]
  refine Finset.sum_eq_zero fun b' _ => ?_
  rw [LinearMap.map_smul, he, smul_zero]

def cen (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E) :
    S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinear (LinearMap.id + nil e c) (LinearMap.id - nil e c)
    (by
      ext x
      simp [nil_eq_zero e c _ (hT_nil e he c x)])
    (by
      ext x
      simp [nil_eq_zero e c _ (hT_nil e he c x)])

theorem cen_apply (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (x : S.V) : cen e he c x = x + nil e c x := rfl

theorem cen_symm_apply (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0)
    (c : Matrix (Fin r) (Fin r) E) (x : S.V) : (cen e he c).symm x = x - nil e c x := rfl

theorem cen_isom (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (hc : cᴴ = -c) : cen e he c ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  have hstar : ∀ a a', starRingEnd E (c a a') = -c a' a := by
    intro a a'
    have h := congrFun (congrFun hc a') a
    rw [starRingEnd_apply]
    simpa [Matrix.conjTranspose_apply] using h
  have hsym : ∀ u v, starRingEnd E (S.hT u v) = S.hT v u := S.herm.eq

  have hnn : ∀ x y, S.hT (nil e c x) (nil e c y) = 0 := by
    intro x y

    rw [nil_apply e c x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_

    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a' _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hT_nil e he c y a, smul_zero]

  have hcross : ∀ x y, S.hT (nil e c x) y + S.hT x (nil e c y) = 0 := by
    intro x y

    simp only [nil_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    LinearMap.map_smul, smul_eq_mul, map_mul, RingHom.id_apply, hstar, hsym]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a' _ => ?_
    ring
  show ∀ x y, S.hT (cen e he c x) (cen e he c y) = S.hT x y
  intro x y
  rw [cen_apply, cen_apply]
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [hnn, add_zero]
  linear_combination hcross x y

theorem nil_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (e : Fin r → S.V)
    (heΛ : ∀ a, e a ∈ Λ) (c : Matrix (Fin r) (Fin r) (𝓞 E)) (x : S.V) (hx : x ∈ Λ) :
    nil e (c.map (algebraMap (𝓞 E) E)) x ∈ Λ := by
  rw [nil_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun a' _ => ?_
  have hd : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    have h' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hΛ
    rw [h']
    exact hx
  have h1 : S.hT (e a') x ∈ (1 : Submodule (𝓞 E) E) := by
    have h2 := (Submodule.mem_iInf _).mp hd (e a')
    have h3 := (Submodule.mem_iInf _).mp h2 (heΛ a')
    exact h3
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
  rw [Matrix.map_apply, ← ho, ← map_mul, algebraMap_smul]
  exact Λ.smul_mem _ (heΛ a)

theorem centre_gen {T : E} (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (heΛ : ∀ a, F.fl.e a ∈ Λ)
    (c : Matrix (Fin r) (Fin r) (𝓞 E))
    (hc : (c.map (algebraMap (𝓞 E) E))ᴴ = -c.map (algebraMap (𝓞 E) E)) :
    ∃ n : S.V ≃ₗ[E] S.V, (n ∈ NLam Λ F ∧ ∀ b, n (frame F b) = frame F b) ∧
      (∀ x ∈ orth S (Xsp F), n x = x) ∧
      ∀ x, n x = x + ∑ a, ∑ a', ((c a a' : E) * S.hT (F.fl.e a') x) • F.fl.e a := by
  have hiso : ∀ a b, S.hT (F.fl.e a) (F.fl.e b) = 0 := F.fl.e_iso

  have hXz : ∀ a', ∀ x ∈ Xsp F, S.hT (F.fl.e a') x = 0 := by
    intro a' x hx
    have hle : Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a')) := by
      show Submodule.span E (Set.range F.fl.e) ≤ _
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact LinearMap.mem_ker.mpr (hiso a' b)
    exact LinearMap.mem_ker.mp (hle hx)
  have hXe : ∀ a, F.fl.e a ∈ Xsp F := by
    intro a
    show F.fl.e a ∈ Submodule.span E (Set.range F.fl.e)
    exact Submodule.subset_span ⟨a, rfl⟩

  have hfix : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x = x := by
    intro x hx
    rw [cen_apply, nil_eq_zero _ _ _ ?_, add_zero]
    intro a'
    have h2 := (Submodule.mem_iInf _).mp hx (F.fl.e a')
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h2 (hXe a'))

  have hframe : ∀ b, cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) (frame F b) = frame F b := by
    intro b
    rw [cen_apply, nil_eq_zero _ _ _ ?_, add_zero]
    intro a'
    induction b using Fin.lastCases with
    | last => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using F.fl.z_orth a'
    | cast i => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using hiso a' i

  have hflag : ∀ j, ∀ x ∈ Xflag F (j + 1),
      cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xflag F j := by
    intro j x hx
    have hle : Xflag F (j + 1) ≤ Xsp F := by
      show Submodule.span E (F.fl.e '' {i | i.1 < j + 1}) ≤ Submodule.span E (Set.range F.fl.e)
      exact Submodule.span_mono (Set.image_subset_range _ _)
    rw [cen_apply, nil_eq_zero _ _ _ (fun a' => hXz a' x (hle hx)), add_zero, sub_self]
    exact zero_mem _
  have horth : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xsp F := by
    intro x hx
    rw [hfix x hx, sub_self]
    exact zero_mem _

  have hmap : Formalism.HermitianLatticesTheory.gmap (cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E))) Λ = Λ := by
    show Submodule.map _ Λ = Λ
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x ∈ Λ
      rw [cen_apply]
      exact Λ.add_mem hx (nil_mem Λ hΛ _ heΛ c x hx)
    · intro y hy
      refine Submodule.mem_map.mpr ⟨y - nil F.fl.e (c.map (algebraMap (𝓞 E) E)) y,
        Λ.sub_mem hy (nil_mem Λ hΛ _ heΛ c y hy), ?_⟩
      show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) _ = y
      rw [← cen_symm_apply F.fl.e hiso _ y]
      exact LinearEquiv.apply_symm_apply _ y
  have hN : cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) ∈ NLam Λ F := by
    simp only [NLam, IsAutLam, Set.mem_setOf_eq]
    exact ⟨⟨cen_isom _ _ _ hc, hmap⟩, hflag, horth⟩
  refine ⟨cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)), ⟨hN, hframe⟩, hfix, fun x => ?_⟩
  rw [cen_apply, nil_apply]
  rfl

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem centralMap_mem_integralUnipotentFixingFrame : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (Λ : LatV D), Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ → (∀ a, F.fl.e a ∈ Λ) → ∀ c : Matrix (Fin D.R.rS) (Fin D.R.rS) (𝓞 D.host.E), (c.map (algebraMap (𝓞 D.host.E) D.host.E))ᴴ = -c.map (algebraMap (𝓞 D.host.E) D.host.E) → ∃ n ∈ N1 D Λ F, (∀ x ∈ orth (hS D) (Xsp F), n x = x) ∧ ∀ x, n x = x + ∑ a, ∑ a', ((c a a' : D.host.E) * (hS D).hT (F.fl.e a') x) • F.fl.e a := by
  intro D T F Λ hΛ heΛ c hc
  obtain ⟨n, h1, hfix, hform⟩ := centre_gen F Λ hΛ heΛ c hc
  exact ⟨n, h1, hfix, hform⟩

end GlobalTheory.LoopC.Centre

end
end

section

namespace GlobalTheory.LoopC.DetCard

section General

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.MainNotions.S

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]
  [IsScalarTower (𝓞 K) K V]

theorem map_latIn {U : Submodule K V} {N : Submodule (𝓞 K) V} (hN : ∀ x ∈ N, x ∈ U) :
    N.toAddSubgroup = (latIn U N).toAddSubgroup.map U.subtype.toAddMonoidHom := by
  ext x
  constructor
  · intro h1
    exact ⟨⟨x, hN x h1⟩, h1, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem idxN_latIn {U : Submodule K V} {A B : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, x ∈ U)
    (hB : ∀ x ∈ B, x ∈ U) : idxN A B = idxN (latIn U A) (latIn U B) := by
  rw [idxN, idxN, map_latIn hA, map_latIn hB, AddSubgroup.relIndex_map_map_of_injective _ _ U.injective_subtype]

theorem isLattice_latIn_span {U : Submodule K V} {N : Submodule (𝓞 K) V} (hN : N.FG)
    (hU : Submodule.span K (N : Set V) = U) : Submodule.IsFullLattice K (latIn U N) := by
  haveI : Submodule.IsLattice K (latIn U N) := by
    apply Submodule.IsLattice.of_fg K
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact Submodule.FG.of_le hN (Submodule.map_comap_le _ _)
  refine ⟨?_⟩
  apply Submodule.map_injective_of_injective U.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  rw [← hU]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hU ▸ Submodule.subset_span hx⟩, hx, rfl⟩

variable [StarRing K]

theorem latIn_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) {U : Submodule K V} {N : Submodule (𝓞 K) V}
    (hU : Submodule.span K (N : Set V) = U) :
    latIn U (Lat.dualInH h N) = dual (hRes h U) (latIn U N) := by
  ext x
  constructor
  · rintro ⟨h1, -⟩
    exact (dualBasic_mem_dual _ _ _).2 fun y hy => (dualBasic_mem_dual _ _ _).1 h1 y hy
  · intro hx
    refine ⟨(dualBasic_mem_dual _ _ _).2 fun z hz => ?_, ?_⟩
    · exact (dualBasic_mem_dual _ _ _).1 hx ⟨z, hU ▸ Submodule.subset_span hz⟩ hz
    · change (x : V) ∈ Submodule.span K (N : Set V)
      rw [hU]
      exact x.2

theorem idxN_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) {U : Submodule K V} {N : Submodule (𝓞 K) V}
    (hU : Submodule.span K (N : Set V) = U) :
    idxN (Lat.dualInH h N) N = discN (hRes h U) (latIn U N) := by
  rw [idxN_latIn (U := U) (A := Lat.dualInH h N) (B := N) (fun x hx => hU ▸ (Submodule.mem_inf.1 hx).2) (fun x hx => hU ▸ Submodule.subset_span hx),
    latIn_dualInH h hU, discN]

theorem general [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hK : IsCMUnram K) (hs : h.IsSymm) (hp : PD h)
    (M : Submodule (𝓞 K) V) (hM : M.FG) (hI : IsIntegralLat h M) :
    1 ≤ idxN (Lat.dualInH h M) M ∧ (idxN (Lat.dualInH h M) M : ℝ) = Lat.latDetH h M ^ 2 ∧
      ∀ P : Submodule (𝓞 K) V, P ≤ M →
        Module.finrank K (Submodule.span K (P : Set V)) = Module.finrank K (Submodule.span K (M : Set V)) →
        1 ≤ idxN M P ∧ Lat.latDetH h P = Lat.latDetH h M * idxN M P := by
  set U := Submodule.span K (M : Set V) with hUdef
  have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
  have hpU : PD (hRes h U) := fun τ x hx => hp τ x fun e => hx (Subtype.ext e)
  have hnU := DetAgree.nondeg_of_pd hpU
  have key : ∀ N : Submodule (𝓞 K) V, N ≤ M → Submodule.span K (N : Set V) = U →
      IsIntLat (hRes h U) (latIn U N) ∧ discN (hRes h U) (latIn U N) ≠ 0 ∧
        Lat.latDetH h N = Real.sqrt (discN (hRes h U) (latIn U N) : ℝ) := by
    intro N hN hU
    have a : IsIntLat (hRes h U) (latIn U N) :=
      ⟨isLattice_latIn_span (hM.of_le hN) hU, fun x hx y hy => hI x (hN hx) y (hN hy)⟩
    have n0 := (DiscOrder.main K U _ hK hsU hnU _ a).1
    refine ⟨a, n0, ?_⟩
    rw [← idxN_dualInH h hU] at n0 ⊢
    rw [Lat.latDetH, DetAgree.genIdxH_eq_idxN _ n0]
    intro x hx
    exact ⟨(dualBasic_mem_dual _ _ _).2 fun y hy => hI y (hN hy) x (hN hx), Submodule.subset_span hx⟩
  obtain ⟨m1, m2, m3⟩ := key M le_rfl rfl
  refine ⟨?_, ?_, fun P hP hr => ?_⟩
  · rw [idxN_dualInH h hUdef.symm]
    exact Nat.pos_of_ne_zero m2
  · rw [idxN_dualInH h hUdef.symm, m3, Real.sq_sqrt (Nat.cast_nonneg _)]
  · have hU : Submodule.span K (P : Set V) = U :=
      Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono hP) hr
    obtain ⟨p1, -, p3⟩ := key P hP hU
    obtain ⟨q1, q2⟩ := (DiscOrder.main K U _ hK hsU hnU _ p1).2.2.1 _ m1 (Submodule.comap_mono hP)
    rw [← idxN_latIn (U := U) (fun x hx => Submodule.subset_span hx)
      (fun x hx => Submodule.subset_span (hP hx))] at q1 q2
    refine ⟨Nat.pos_of_ne_zero q1, ?_⟩
    rw [p3, m3, q2, Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (Nat.cast_nonneg _),
      Real.sqrt_sq (Nat.cast_nonneg _)]

end General

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (M : LatW D), M.FG → IsPosDef (D.sp.X 0).hT → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT M → 1 ≤ idxW D (dualInH (D.sp.X 0).hT M) M ∧ (idxW D (dualInH (D.sp.X 0).hT M) M : ℝ) = detW D M ^ 2 ∧ ∀ P : LatW D, P ≤ M → rkW D P = rkW D M → 1 ≤ idxW D M P ∧ detW D P = detW D M * idxW D M P := by
  intro D M hM hp hI
  exact general (D.sp.X 0).hT D.sp.cm.cmUnram (D.sp.X 0).herm hp M hM hI

end GlobalTheory.LoopC.DetCard
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.encard_gluingHom_kernels_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (Mh : Submodule L.O S.V) (j : ℕ), ((((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) '' {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}).encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1) := by
  first | exact @GlobalTheory.HL.GluingKernels.encard_kernels_le | exact GlobalTheory.HL.GluingKernels.encard_kernels_le | (intros; apply GlobalTheory.HL.GluingKernels.encard_kernels_le <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFamily_trace_volume_const : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → ∀ Yy : Submodule L.O S.V, (Yy = (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O ∨ Yy = (perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))).restrictScalars L.O) → (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup = (Λ' ⊓ Yy).toAddSubgroup.relIndex (Λ ⊓ Yy).toAddSubgroup ∧ (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup ≠ 0 ∧ (S.M d Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup.relIndex (Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup = β := by
  first | exact @GlobalTheory.HL.FamilyVol.family_vol | exact GlobalTheory.HL.FamilyVol.family_vol | (intros; apply GlobalTheory.HL.FamilyVol.family_vol <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → s • x ∈ Λ ∧ L.cj s • x ∈ Λ ∧ s • x' ∈ Λ ∧ L.cj s • x' ∈ Λ ∧ (∃ c ∈ L.O, S.h x' x = algebraMap F E S.th * c) ∧ S.h x x = 0 ∧ S.h x' x' = 0 ∧ S.h u x = 0 ∧ S.h u x' = 0 ∧ x ∈ S.X ∧ x' ∈ S.X' := by
  first | exact @GlobalTheory.HL.MoveFacts.move_facts | exact GlobalTheory.HL.MoveFacts.move_facts | (intros; apply GlobalTheory.HL.MoveFacts.move_facts <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.quadric_character_leak_shares_finite : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (N : ℕ) (R : Finset S.V) (Z : S.V → Prop), S.a + 1 ≤ N → (∀ u, Z u ↔ ∃ c : 𝒪[F], S.h u u = algebraMap F E ((S.ϖ : F) ^ S.a * c)) → (∀ u ∈ R, u ∈ Λ ∧ u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)) → (∀ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) → ∃! w, w ∈ R ∧ ∃ y ∈ Λ, u - w = algebraMap F E ((S.ϖ : F) ^ N) • y) → |((R.filter Z).card : ℝ) - R.card / (S.q : ℝ) ^ S.a| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) ∧ (((R.filter fun u => Z u ∧ ¬ ∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1).card : ℝ) ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a)) ∧ ∀ y : S.V, (∀ u ∈ R, algebraMap F E ((S.ϖ : F) ^ N) * S.h y u ∈ L.O) → (∃ u ∈ R, L.psi0 (S.h y u) ≠ 1) → ‖∑ u ∈ R.filter Z, L.psi0 (S.h y u)‖ ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) := by
  first | exact @GlobalTheory.HL.QuadricShare.shares | exact GlobalTheory.HL.QuadricShare.shares | (intros; apply GlobalTheory.HL.QuadricShare.shares <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.torus_modulus_unipotentRadical_unitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm → (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) → (∀ s, dOp (umat (a s)) ≤ |s|) → (∀ s, ∀ m ∈ NW ε W, a s * m * (a s)⁻¹ ∈ NW ε W) → ∃ κ : ℝ, |κ| ≤ 8 * n * rkR ε ∧ ∀ s, ν.map (fun m => a s * m * (a s)⁻¹) = ENNReal.ofReal (Real.exp (κ * s)) • ν := by
  first | exact @GlobalTheory.Dec.TorusModulus.torus_modulus | exact GlobalTheory.Dec.TorusModulus.torus_modulus | (intros; apply GlobalTheory.Dec.TorusModulus.torus_modulus <;> assumption)
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Count.PerpSize

open GlobalTheory.Count.PerpStep

theorem inv_le_sizeQ_perp : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → ∀ N, perpIn I x R < N → N ≤ lamX I x → hi⁻¹ ≤ sizeQ (bas I) (frm I x) N (perpIn I x R) := by
  intro I x R hi hR hhi hL N hPN hNA
  obtain ⟨-, hA, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨htc, -, -, -, hw⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hw v).1
  obtain ⟨-, -, -, hm⟩ := GlobalTheory.Count.PerpStep.main I x
  obtain ⟨N', n1, n2, n3, n4⟩ := nd_sat (bas I) (frm I x) hX hA hNA
  obtain ⟨sP, rP, ppR, -, -⟩ := hm R R hR hR le_rfl
  obtain ⟨sS, rS, ppN, -, -⟩ := hm N' N' n2 n2 le_rfl
  have hPN' : perpIn I x R ≤ N' := hPN.le.trans n1
  obtain ⟨-, -, -, hle, hq⟩ := hm _ N' sP n2 hPN'
  rw [ppR] at hle hq
  have hfg : ∀ {M}, M ≤ lamX I x → M.FG := fun h => Submodule.FG.of_le hA h
  have hR0 : R ≠ ⊥ := by
    intro e
    have h1 : perpIn I x N' = R := by
      rw [e] at hle ⊢
      exact le_bot_iff.1 hle
    rw [h1] at ppN
    exact (lt_of_lt_of_le hPN n1).ne ppN
  rw [htQ_eq _ _ hX _ _ (hfg hR.1) (sat_mono _ _ sS hle hR.1),
    htQ_eq _ _ hX _ _ (hfg n2.1) (sat_mono _ _ sP hPN' n2.1), ← Real.exp_neg] at hq
  have hq' := Real.exp_injective hq
  obtain ⟨l0, lb⟩ := largest_bound (bas I) (frm I x) hX (hfg hR.1) hR0 hle
  have hd := rk_lt (bas I) (frm I x) hX hA sP hPN hNA
  have r1 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg hR.1)).2.1
  have r2 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg sP.1)).2.1
  have r3 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg sS.1)).2.1
  have r4 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg n2.1)).2.1
  have hrk : rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) +
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R =
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') +
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N := by
    rw [← n3, r1, r2, r3, r4, ← mul_add, ← mul_add, rP, rS]
  have hrk' : (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R : ℝ) -
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') =
      (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N : ℝ) -
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hrk
    push_cast at h
    linarith
  rw [hrk'] at lb
  rw [log_sizeQ (bas I) (frm I x) hX hA sP hPN hNA, ← Real.log_le_iff_le_exp (inv_pos.2 hhi),
    le_div_iff₀ (sub_pos.2 hd), Real.log_inv]
  have h4 := Real.log_le_log l0 hL
  have h5 := mul_le_mul_of_nonneg_right h4 (sub_pos.2 hd).le
  linarith

end GlobalTheory.Count.PerpSize
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

theorem _root_.GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint : ∀ (I : AutInst) (x : I.GA), ht (bas I) (frm I x) (lamX I x) = 1 ∧ (1 ≤ I.n → largestSize (bas I) (frm I x) (lamX I x) = (least I x)⁻¹) ∧ (∀ t : ℝ, 0 < t → perpIn I x (stepLe I x t) = stepLt I x t⁻¹ ∧ perpIn I x (stepLt I x t) = stepLe I x t⁻¹) ∧ ∀ S S' : Submodule (𝓞 I.E) (Fin I.n → I.E), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S' → S ≤ S' → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (perpIn I x S) ∧ rkK (perpIn I x S) + rkK S = I.n ∧ perpIn I x (perpIn I x S) = S ∧ perpIn I x S' ≤ perpIn I x S ∧ htQ (bas I) (frm I x) (perpIn I x S) (perpIn I x S') = (htQ (bas I) (frm I x) S' S)⁻¹ := by
  first | exact @GlobalTheory.Count.PerpStep.main | exact GlobalTheory.Count.PerpStep.main | (intros; apply GlobalTheory.Count.PerpStep.main <;> assumption)
end
