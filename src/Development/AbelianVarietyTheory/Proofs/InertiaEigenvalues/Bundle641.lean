module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle612
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle275
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle613
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.WhitCols

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E]

theorem avg_eq_setIntegral {ι : Type} [Fintype ι] (Φ : (ι → Ad E) → ℂ) (hΦ : Per (ratV E ι) Φ) :
    avg (ratV E ι) Φ = ∫ x in vecDomain E ι, Φ x ∂vecMeasure E ι := by
  have hF : IsAddFundamentalDomain (ratV E ι) (vecDomain E ι) (vecMeasure E ι) := isAddFundamentalDomain_vecDomain
  obtain ⟨-, -, -, h⟩ := GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg (ι → Ad E) (ratV E ι) (isCoLat_ratV E ι)
    (vecMeasure E ι) (vecDomain E ι) inferInstance hF Φ hΦ
  rw [h, vecMeasure_vecDomain]
  simp

def colIx {a k : ℕ} (hk : k < a) : Fin k ≃ UnipotentBlockColumnIndex a k k where
  toFun i := ⟨(⟨i.1, by omega⟩, ⟨k, hk⟩), i.2, le_rfl, le_rfl⟩
  invFun t := ⟨t.1.1.1, t.2.1⟩
  left_inv i := rfl
  right_inv t := by
    obtain ⟨⟨i, j⟩, h1, h2, h3⟩ := t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      dsimp only at h1 h2 h3 ⊢
      omega

def colHom {a k : ℕ} (hk : k < a) : (Fin k → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex a k k → Ad E) where
  toFun x := fun t => x ((colIx hk).symm t)
  invFun y := fun i => y (colIx hk i)
  left_inv x := by funext i; simp
  right_inv y := by funext t; simp
  map_add' x y := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

theorem colHom_mem_iff {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    colHom hk x ∈ ratV E (UnipotentBlockColumnIndex a k k) ↔ x ∈ ratV E (Fin k) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun i => c (colIx hk i), funext fun i => ?_⟩
    have := congrFun hc (colIx hk i)
    simpa [colHom] using this
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c ((colIx hk).symm t), rfl⟩

theorem blkU_colHom {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    (blkU (colHom hk x) : GL (Fin a) (Ad E)) = colGL k x := by
  refine Units.ext ?_
  ext i j
  rw [blkU_apply]
  simp only [colGL, coe_uGL, uMat_apply, colX_apply, Matrix.one_apply, colHom, colIx]
  split_ifs <;> first | rfl | simp_all
  all_goals (exfalso; simp only [Fin.ext_iff, Fin.lt_def, Fin.le_def] at *; omega)

theorem dot_colHom {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    dot (eLast a k) (colHom hk x) = pair (lastVec k) x := by
  rw [dot, pair, ← (colIx hk).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [colHom, eLast, lastVec, colIx, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  by_cases h : (i : ℕ) + 1 = k <;> simp [h]

theorem colT_eq_stepCoeff {a k : ℕ} (hk : k < a) {F : GA E a → ℂ} (hc : Continuous F)
    (hl : ∀ (ξ : Fin k → E) g, F (AdelicGLn.diagonal E a (colGL k ξ) * g) = F g) (g : GA E a) :
    colT (GlobalTheory.StdCharConductor.psi E) k F g = stepCoeff k F g := by
  have hψ := GlobalTheory.StdCharConductor.stdPsi_psi E
  have hl' : ∀ (c : UnipotentBlockColumnIndex a k k → E) g, F (ratGL E a (blkU c) * g) = F g := by
    intro c g
    have e : ratGL E a (blkU c) = AdelicGLn.diagonal E a (colGL k (fun i => c (colIx hk i))) := by
      rw [ratGL_blkU, diagonal_colGL, ← blkU_colHom hk]
      congr 1
      funext t
      simp [colHom]
    rw [e, hl]
  have hP := per_coef hψ (eLast a k) hc hl' g
  have hP' : Per (ratV E (Fin k)) (fun x => (fun y : UnipotentBlockColumnIndex a k k → Ad E =>
      GlobalTheory.StdCharConductor.psi E (-dot (eLast a k) y) * F (blkU y * g)) (colHom hk x)) := by
    refine ⟨hP.1.comp (colHom hk).continuous_toFun, fun γ hγ x => ?_⟩
    simp only [map_add (f := _)]
    exact hP.2 _ ((colHom_mem_iff hk γ).2 hγ) _
  unfold colT coefF
  rw [← avg_equiv (Fin k → Ad E) (UnipotentBlockColumnIndex a k k → Ad E) (ratV E (Fin k)) (ratV E (UnipotentBlockColumnIndex a k k)) (isCoLat_ratV E _)
    (isCoLat_ratV E _) (colHom hk) (colHom_mem_iff hk) _ hP, avg_eq_setIntegral _ hP']
  unfold stepCoeff vecCoeff
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [blkU_colHom, dot_colHom, GlobalTheory.StdCharConductor.psi_apply]
  ring

def IsUU {j : ℕ} (h : Matrix (Fin j) (Fin j) E) : Prop :=
  ∀ i l : Fin j, l ≤ i → h i l = (1 : Matrix (Fin j) (Fin j) E) i l

theorem IsUU.isLastRowUnit {j : ℕ} {h : Matrix (Fin j) (Fin j) E} (hh : IsUU h) : IsLastRowUnit h := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · funext c; exact c.elim0
  · funext c
    have hc : c ≤ (⟨j - 1, by omega⟩ : Fin j) := by rw [Fin.le_def]; show (c : ℕ) ≤ j - 1; omega
    rw [vecMul_lastVec _ _ hj, hh _ _ hc, Matrix.one_apply]
    simp only [lastVec, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

omit [NumberField E] in
theorem isUU_blockMat {j : ℕ} {h : Matrix (Fin j) (Fin j) E} (hh : IsUU h) :
    IsUU (blockMat (n := j + 1) (Nat.le_succ j) h) := by
  intro i l hli
  rw [blockMat_apply]
  split_ifs with ha hb
  · rw [hh _ _ (by rw [Fin.le_def] at hli ⊢; exact hli), Matrix.one_apply, Matrix.one_apply]
    simp only [Fin.ext_iff]
  · exfalso; rw [Fin.le_def] at hli; omega
  all_goals simp_all [Matrix.one_apply]

omit [NumberField E] in
theorem isUU_colX {j : ℕ} (ξ : Fin j → E) : IsUU (uMat (colX (n := j + 1) j ξ)) := by
  intro i l hli
  rw [uMat_apply, Matrix.one_apply]
  split_ifs <;> first | rfl | (exfalso; simp only [Fin.lt_def, Fin.le_def] at *; omega)

theorem partialCoeff_uu {n : ℕ} {f : GA E n → ℂ}
    (hf : ∀ γ ∈ mirU E n 0, ∀ g, f (ratGL E n γ * g) = f g) :
    ∀ (m j : ℕ), n - j = m → ∀ (hj : j ≤ n) (h : GL (Fin j) E), IsUU (h : Matrix (Fin j) (Fin j) E) → ∀ g,
      partialCoeff f j (AdelicGLn.diagonal E n (blockGL hj h) * g) = partialCoeff f j g := by
  intro m
  induction m with
  | zero =>
    intro j hjm hj h hh g
    obtain rfl : j = n := by omega
    rw [partialCoeff_self]
    have : blockGL hj h = h := Units.ext (by rw [coe_blockGL]; exact blockMat_self _)
    rw [this]
    exact hf h (mem_mirU.2 fun i k _ hk => hh i k hk) g
  | succ m ih =>
    intro j hjm hj h hh g
    have hjn : j < n := by omega
    rw [partialCoeff_of_lt f hjn]
    have hB : ∀ g, partialCoeff f (j + 1) (AdelicGLn.diagonal E n (blockGL hjn.le h) * g) =
        partialCoeff f (j + 1) g := by
      intro g
      rw [← blockGL_blockGL (Nat.le_succ j) hjn]
      exact ih (j + 1) (by omega) hjn _ (isUU_blockMat hh) g
    have hC : ∀ (ξ : Fin j → E) g, partialCoeff f (j + 1) (AdelicGLn.diagonal E n (colGL j ξ) * g) =
        partialCoeff f (j + 1) g := by
      intro ξ g
      rw [colGL_eq_blockGL (Nat.lt_succ_self j) hjn]
      exact ih (j + 1) (by omega) hjn _ (isUU_colX _) g
    rw [stepCoeff_diagonal_blockGL hjn h hB hC g, hh.isLastRowUnit]
    rfl

theorem colT_partialCoeff {m : ℕ} {f : GA E (m + 1) → ℂ} (hc : Continuous f)
    (hf : ∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) {k : ℕ} (hk : k < m + 1) :
    colT (GlobalTheory.StdCharConductor.psi E) k (partialCoeff f (k + 1)) = partialCoeff f k := by
  funext g
  rw [partialCoeff_of_lt f hk]
  refine colT_eq_stepCoeff hk (continuous_partialCoeff hc _) (fun ξ g => ?_) g
  rw [colGL_eq_blockGL (Nat.lt_succ_self k) hk]
  exact partialCoeff_uu hf _ (k + 1) rfl hk _ (isUU_colX _) g

theorem whit_partialCoeff {m : ℕ} {f : GA E (m + 1) → ℂ} (hc : Continuous f)
    (hf : ∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) :
    ∀ i, i ≤ m → GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) i (partialCoeff f (i + 1)) = partialCoeff f 1
  | 0, _ => rfl
  | i + 1, hi => by
    rw [GlobalTheory.CuspGeneric.whit_succ, colT_partialCoeff hc hf (by omega : i + 1 < m + 1),
      whit_partialCoeff hc hf i (by omega)]

theorem whit_eq_colWhit : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (f : GA E (m + 1) → ℂ), Continuous f →
    (∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) →
    ∀ g, GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := by
  intro E _ _ m f hc hf g
  rw [GlobalTheory.JSW.whit, whittaker_eq_partialCoeff hc (Nat.succ_pos m), ← whit_partialCoeff hc hf m le_rfl,
    partialCoeff_self]

end GlobalTheory.WhitCols
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix GlobalTheory.PRep GlobalTheory.Published GlobalTheory.UnitaryBC
open GlobalTheory.CuspRep.LocEx

namespace GlobalTheory.DiscLocEx

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def opD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (o : Op E a) : Module.End ℂ V := (act o).restrict (hV o)

def finPartD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) : Representation ℂ (GL (Fin a) (Af E)) V :=
  GlobalTheory.PRep.sub (finRep E a) V fun k => hV (.fin k)

def locRepD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E)) :
    Representation ℂ (GL (Fin a) (w.adicCompletion E)) V :=
  (finPartD hV).comp (locGL E a w)

theorem isSmooth_finPartD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (ha : ∀ φ ∈ V, IsAutForm φ) :
    IsSmooth (finPartD hV) := fun φ => by
  convert (ha _ φ.2).level using 1
  ext k
  exact Subtype.ext_iff

theorem isSmooth_locRepD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (ha : ∀ φ ∈ V, IsAutForm φ)
    (w : HeightOneSpectrum (𝓞 E)) : IsSmooth (locRepD hV w) := fun φ =>
  (isSmooth_finPartD hV ha φ).preimage (CuspSub.continuous_locGL w)

theorem exists_scalarD {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem nullPart_opD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (o : Op E a) {x : V} (hx : x ∈ nullPart (locRepD hV w) K) : opD hV o x ∈ nullPart (locRepD hV w) K := by
  cases o with
  | fin k =>
    have h1 := nullPart_act _ K (GeneralLinearGroup.map (pLoc E w) k) (nullPart_comm _ K
      (finPartD hV ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
      simp only [locRepD, MonoidHom.comp_apply]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        LocUniq.comm_locGL w (map_pLoc_inv_mul w k)]) hx)
    rwa [locRepD, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1
  | cpt k =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem eq_bot_of_fixedD {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) (w : HeightOneSpectrum (𝓞 E))
    {K : Subgroup (GL (Fin a) (w.adicCompletion E))} (hK : IsCompact (K : Set (GL (Fin a) (w.adicCompletion E))))
    {φ : V} (h0 : φ ≠ 0) (hφ : φ ∈ fixed (locRepD hV.stable w) K) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, locRepD hV.stable w g v ∈ W) (h : W ⊓ fixed (locRepD hV.stable w) K = ⊥) : W = ⊥ := by
  have hi := Submodule.map_injective_of_injective V.injective_subtype
  rcases hV.irred ((nullPart (locRepD hV.stable w) K).map V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, nullPart_opD hV.stable w K o hx, rfl⟩) with h1 | h1
  · have h2 : nullPart (locRepD hV.stable w) K = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    exact le_bot_iff.1 (h2 ▸ le_nullPart (isSmooth_locRepD hV.stable hV.aut w) hK W hW h)
  · have h2 : nullPart (locRepD hV.stable w) K = ⊤ := hi (h1.trans (Submodule.map_subtype_top _).symm)
    exact absurd (eq_zero_of_mem_nullPart (isSmooth_locRepD hV.stable hV.aut w) hK hφ (h2 ▸ Submodule.mem_top)) h0

def typePartD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) : Submodule ℂ V where
  carrier := {ψ | (∀ k ∈ L, GeneralLinearGroup.map (pLoc E w) k = 1 → finPartD hV k ψ = ψ) ∧
    ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy => ⟨fun k h1 h2 => by rw [map_add (f := _), hx.1 k h1 h2, hy.1 k h1 h2],
    fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => map_zero _, fun _ => zero_mem _⟩
  smul_mem' := fun c _ hx => ⟨fun k h1 h2 => by rw [map_smul, hx.1 k h1 h2],
    fun g => Submodule.smul_mem _ c (hx.2 g)⟩

theorem typePartD_act {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (g : GL (Fin a) (w.adicCompletion E))
    (x : V) (hx : x ∈ typePartD hV w L ρ) : locRepD hV w g x ∈ typePartD hV w L ρ := by
  refine ⟨fun k h1 h2 => ?_, fun y => ?_⟩
  · rw [locRepD, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, LocUniq.comm_locGL w h2, map_mul,
      Module.End.mul_apply, hx.1 k h1 h2]
  · convert hx.2 (y * finGL E a (locGL E a w g)) using 2 with k
    change x.1.1 (y * infGL E a _ * finGL E a _) = x.1.1 (y * finGL E a _ * infGL E a _)
    rw [mul_assoc, mul_assoc, infGL_comm]

theorem finiteDimensional_typePartD (h : AutomorphicFormsFiniteGL) {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E))
    {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {ρ : Representation ℂ (Kinf E a) W}
    (hρ : AutFin.IsContRep ρ) (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (hK : IsOpen (K : Set (GL (Fin a) (w.adicCompletion E)))) :
    FiniteDimensional ℂ ↥(typePartD hV.stable w L ρ ⊓ fixed (locRepD hV.stable w) K) := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ V, cap τ u φ = c • φ := fun τ u =>
    exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := h E a (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w)))
    (hL.inter ((hK.inter (hL.preimage (CuspSub.continuous_locGL w))).preimage (continuous_map_pLoc w))) W ρ hρ c
  refine FiniteDimensional.of_injective ((V.subtype ∘ₗ (typePartD hV.stable w L ρ ⊓
    fixed (locRepD hV.stable w) K).subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms
      (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w))) ρ c))
    fun v => Submodule.subset_span ⟨hV.aut _ v.1.2, fun k hk => ?_, v.2.1.2, fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  have h1 := v.2.1.1 _ (L.mul_mem (L.inv_mem hk.2.2) hk.1) (map_pLoc_inv_mul w k)
  have h2 := mem_fix.1 v.2.2 _ hk.2.1
  have h3 : finPartD hV.stable k v.1 = v.1 := by
    rw [← mul_inv_cancel_left (locGL E a w (GeneralLinearGroup.map (pLoc E w) k)) k, map_mul, Module.End.mul_apply, h1]
    exact h2
  exact congrArg Subtype.val h3

theorem exists_irred_sub (h : AutomorphicFormsFiniteGL) {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E)) :
    ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), (∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧
      ∀ g v, f (σ.ρ g v) = locRepD hV.stable w g (f v)) ∧ IsAdmissible σ.ρ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  have h0' : (⟨φ, hφ⟩ : V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have hL : IsOpen (stab (finPartD hV.stable) ⟨φ, hφ⟩ : Set (GL (Fin a) (Af E))) :=
    isSmooth_finPartD hV.stable hV.aut _
  obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
  have : FiniteDimensional ℂ (orbSpan φ) := (hV.aut φ hφ).kfin
  refine exists_irred (isSmooth_locRepD hV.stable hV.aut w) ho (eq_bot_of_fixedD hV w hc h0' (mem_fix.2 hK))
    (typePartD hV.stable w (stab (finPartD hV.stable) ⟨φ, hφ⟩) (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)))
    (typePartD_act hV.stable w _ _)
    ((Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩, ⟨fun k hk _ => hk, ?_⟩, h0'⟩)
    (finiteDimensional_typePartD h hV w hL (isContRep_sub _ _))
  exact AutFinGL.type_of_map (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)) (orbSpan φ).subtype (fun _ _ => rfl)
    ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩

end GlobalTheory.DiscLocEx


open GlobalTheory.DiscSpec GlobalTheory.SmGL in
theorem GlobalTheory.DiscLocEx.exists_isLocCompGL : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (N : ℕ), ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V →
    ∀ w : HeightOneSpectrum (𝓞 E), ∃ σ' , IsLocCompGL V w σ' := by
  intro h E _ _ _ N V hV w
  obtain ⟨σ, ⟨f, hf0, hf⟩, -⟩ := GlobalTheory.DiscLocEx.exists_irred_sub h hV w
  refine ⟨σ, V.subtype ∘ₗ f, fun e => hf0 (LinearMap.ext fun v => Subtype.ext ?_), fun v => (f v).2,
    fun g v => congrArg Subtype.val (hf g v)⟩
  exact LinearMap.congr_fun e v
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory


theorem _root_.GlobalTheory.T.heckeChar_local_eq_one_of_trivial_on_norms_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ε : Formalism.L2.Host.HChar (maximalRealSubfield E)),
    compNorm E ε = 1 → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∀ x, ε.loc v x = 1 := by
  first | exact @GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one | exact GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one | (intros; apply GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one <;> assumption)
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst

namespace GlobalTheory.GalOfCusp

def LocalGlobalAboveL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)), w ∈ placesOver E l → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
      (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
      ∀ rc : IrrGL (k := w.adicCompletion E) → WD h, IsRec h rc →
        wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

end GlobalTheory.GalOfCusp

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.ainf_exists_mul_eq_pow_smul_of_mod_lPow : ∀ (l : ℕ) [Fact l.Prime] (d M : ℕ) (τ : Ainf l) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ n, ∃ Q : Matrix (Fin d) (Fin d) (Ainf l), ∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * Q.map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → ∃ Y' : Matrix (Fin d) (Fin d) (Ainf l), Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  first | exact @GlobalTheory.AinfInvLim.exists_mul_eq_smul_one | exact GlobalTheory.AinfInvLim.exists_mul_eq_smul_one | (intros; apply GlobalTheory.AinfInvLim.exists_mul_eq_smul_one <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.dcris_strict_hodgeFiltration_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → (Function.Surjective π → IsCrys (P.PD K) ρ₁ → ∀ a : ℤ, (FilCris (P.PD K) ρ₁ a).map (AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) = FilCris (P.PD K) ρ₂ a) ∧ (Function.Injective π → ∀ a : ℤ, ∀ y ∈ Dcris (P.PD K) ρ₁, AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) y ∈ FilCris (P.PD K) ρ₂ a → y ∈ FilCris (P.PD K) ρ₁ a) := by
  first | exact @GlobalTheory.Per.CrisStrict.dcris_strict | exact GlobalTheory.Per.CrisStrict.dcris_strict | (intros; apply GlobalTheory.Per.CrisStrict.dcris_strict <;> assumption)
end
