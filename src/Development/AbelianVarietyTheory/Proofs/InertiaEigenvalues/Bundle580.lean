module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
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
import Mathlib.RingTheory.AdicCompletion.Completeness
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.GalY

private theorem witt_padicInt_hom_ext (l : ℕ) [Fact l.Prime] {k : Type} [CommRing k] [CharP k l]
    (f g : ℤ_[l] →+* WittVector l k) : f = g := by
  refine RingHom.ext fun x => sub_eq_zero.1 (WittVector.ext fun n => ?_)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (n + 1) x)
  have hx : x = (x.appr (n + 1) : ℤ_[l]) + y * (l : ℤ_[l]) ^ (n + 1) := by rw [hy]; ring
  have h : f x - g x = (f y - g y) * (l : WittVector l k) ^ (n + 1) := by
    rw [hx]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [h, WittVector.zero_coeff]
  exact WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self n)

theorem inclW_zA (l : ℕ) [Fact l.Prime] (z : ℤ_[l]) : inclW l (Per.zA l z) = algebraMap ℤ_[l] (WCb l) z := by
  exact RingHom.congr_fun
    (witt_padicInt_hom_ext l ((inclW l).comp (Per.zA l)) (algebraMap ℤ_[l] (WCb l))) z

end GlobalTheory.BKLim.GalY


open GlobalTheory.BKLim.GalY in
theorem GlobalTheory.BKLim.gal_tauPow_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) := by
  intro l _ K bk τ N d ρ F Y hY g
  apply Matrix.map_injective (f := inclW l) (GlobalTheory.Prism.inclW_injective)
  have hsm : ∀ {m n : Type} (c : Ainf l) (M : Matrix m n (Ainf l)), (c • M).map (inclW l) = inclW l c • M.map (inclW l) :=
    fun c M => Matrix.ext fun i j => by simp
  have hz : ((ρ g).map (Per.zA l)).map (inclW l) = zW (ρ g) :=
    Matrix.ext fun i j => inclW_zA l _
  have hg' : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) :=
    Matrix.ext fun i j => (GlobalTheory.Prism.galW_inclW _ _).symm
  have hgal := F.gal g
  show Matrix.map _ (inclW l) = Matrix.map _ (inclW l)
  have hsg : ∀ (c : WCb l) (M : Matrix (Fin d) (Fin d) (WCb l)),
      (c • M).map (galW l (g : GQ l)) = galW l (g : GQ l) c • M.map (galW l (g : GQ l)) :=
    fun c M => Matrix.ext fun i j => by simp
  rw [hsm, hsm, Matrix.map_mul, Matrix.map_mul, hz, hg', hY, hsg, map_pow, map_pow, map_pow, GlobalTheory.Prism.galW_inclW,
    Matrix.mul_smul, hgal, Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem wseed_of_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (s : Seed bk d ρ τ), ∃ s' : WSeed bk d ρ τ, ∀ g, s'.κ g = 1 := by
  intro l _ K bk τ _ d ρ s
  refine ⟨{ s with κ := fun _ => 1, gal := ?_, fix := fun _ _ => rfl, nopole := ?_, log := ?_ }, fun _ => rfl⟩
  · intro g G hG
    rw [Matrix.mul_one]
    exact s.gal g G hG
  · intro g G hG i j
    obtain ⟨k, hk⟩ := s.nopole bk.ι ((ainfHom K g).comp bk.ι)
    have h1 := map_dvd bk.iA (hk i j)
    have hX : (s.X.map bk.iS).map G = s.X.map (fun x => bk.iA (Per.σA (g : GQ l) (bk.ev x))) := by
      ext a b
      simp only [Matrix.map_apply, BK.iS, RingHom.comp_apply]
      exact hG.ext _
    have hu : IsUnit (bk.iA ((l : Ainf l) ^ k)) := by
      rw [map_pow, map_natCast]
      exact (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow k
    change bk.iA ((bk.ev bk.E) ^ (2 * s.N)) ∣ bk.iA ((l : Ainf l) ^ k * (s.X'.map bk.ev * s.X.map (fun x => Per.σA (g : GQ l) (bk.ev x))) i j) at h1
    rw [map_mul] at h1
    rw [Matrix.mul_one, hX]
    have h2 := (hu.dvd_mul_left).1 h1
    convert h2 using 1
    · simp only [BK.iS, RingHom.comp_apply, map_pow]

    · simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, BK.iS, RingHom.comp_apply]
  · intro m
    refine ⟨0, 1, fun i j => by simp, fun g G hG i j => ?_⟩
    simp [Matrix.map_one]

end GlobalTheory.BKLim
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

theorem mat_cancel_left {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (B M M' : Matrix n n R) (hB : B.det ∈ nonZeroDivisors R) (h : B * M = B * M') : M = M' := by
  have h2 : B.det • M = B.det • M' := by
    have e : ∀ N : Matrix n n R, B.det • N = B.adjugate * (B * N) := fun N => by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [e, e, h]
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  have h4 : (M i j - M' i j) * B.det = 0 := by rw [sub_mul, mul_comm (M i j), mul_comm (M' i j), h3, sub_self]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hB) _ h4)

theorem bas_map_cancel_left : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (C : Type) [CommRing C] (F : bk.DS bk.ρ₀ →+* C), F (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈ nonZeroDivisors C → ∀ M M' : Matrix (Fin d) (Fin d) C, ht.bas.map F * M = ht.bas.map F * M' → M = M' := by
  intro l _ K bk d ρ τ s ht C _ F hE M M' h
  set G : bk.S →+* C := F.comp (toDisc l (X : bk.S) bk.ρ₀) with hG
  have hbas : ht.bas.map F = s.X.map G * ht.Z.map F := by
    rw [bas, Matrix.map_mul, Matrix.map_map]; rfl
  have hl : IsUnit (G (l : bk.S)) := by
    rw [map_natCast]
    have := (isUnit_l_disc l (X : bk.S) bk.ρ₀).map F
    rwa [map_natCast] at this
  have hc : G ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) ∈ nonZeroDivisors C := by
    rw [map_mul, map_pow, map_pow]
    exact Submonoid.mul_mem _ (Submonoid.pow_mem _ hl.mem_nonZeroDivisors _) (Submonoid.pow_mem _ hE _)
  have hdet : (s.X.map G).det * (s.X'.map G).det = G ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) ^ d := by
    rw [← Matrix.det_mul, ← Matrix.map_mul, s.X_mul, Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (map_zero G),
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hX : (s.X.map G).det ∈ nonZeroDivisors C :=
    (mul_mem_nonZeroDivisors.1 (hdet ▸ Submonoid.pow_mem _ hc _)).1
  have hZ : IsUnit (ht.Z.map F).det := by
    have := ht.Z_unit.map F.mapMatrix
    exact (Matrix.isUnit_iff_isUnit_det _).1 this
  refine mat_cancel_left _ M M' ?_ h
  rw [hbas, Matrix.det_mul]
  exact Submonoid.mul_mem _ hX hZ.mem_nonZeroDivisors

end GlobalTheory.BSP.Height
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

def Layer.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [Group Δ] (j : Δ →* Γ) {a d' : ℕ} {L₀ : FinExt l}
    {Cl : Set (Γ →* GL (Fin a) (Om l))} {ρ' : Γ →* GL (Fin d') ℤ_[l]} (Y : Layer L₀ Cl ρ') :
    Layer L₀ ((fun ρ => ρ.comp j) '' Cl) (ρ'.comp j) where
  m := Y.m
  rep k := (Y.rep k).comp j
  mem k := ⟨Y.rep k, Y.mem k, rfl⟩
  L := Y.L
  le := Y.le
  rep_mem k g := Y.rep_mem k (j g)
  b := Y.b
  b_mem := Y.b_mem
  indep := Y.indep
  span := Y.span
  e := Y.e
  reads k := ⟨fun g => (Y.reads k).equi (j g), (Y.reads k).one⟩
  c := Y.c

def Tower.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [Group Δ] (j : Δ →* Γ) {d : ℕ}
    {ρ : Γ →* GL (Fin d) ℤ_[l]} (T : Tower ρ) : Tower (ρ.comp j) where
  d' := T.d'
  ρ' n := (T.ρ' n).comp j
  Pi := T.Pi
  onto n := ⟨fun g => (T.onto n).equi (j g), (T.onto n).surj⟩
  f := T.f
  f_equi n g := T.f_equi n (j g)
  f_Pi := T.f_Pi

def Cover.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ]
    (j : Δ →* Γ) (hj : Continuous j) {a : ℕ} {L₀ : FinExt l} {r : Γ →* GL (Fin a) (Om l)}
    {Cl : Set (Γ →* GL (Fin a) (Om l))} (C : Cover L₀ r Cl) :
    Cover L₀ (r.comp j) ((fun ρ => ρ.comp j) '' Cl) where
  d := C.d
  ρ := C.ρ.comp j
  cont := C.cont.comp hj
  b := C.b
  e := C.e
  reads := ⟨fun g => C.reads.equi (j g), C.reads.one⟩
  tw := C.tw.pull j
  cont' n := (C.cont' n).comp hj
  lay n := (C.lay n).pull j
  unit := C.unit
  trace := C.trace

theorem cover_pull : ∀ (l : ℕ) [Fact l.Prime] (Γ Δ : Type) [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ] (j : Δ →* Γ), Continuous j → ∀ (a : ℕ) (L₀ : FinExt l) (r : Γ →* GL (Fin a) (Om l)) (Cl : Set (Γ →* GL (Fin a) (Om l))), Cover L₀ r Cl → Nonempty (Cover L₀ (r.comp j) ((fun ρ => ρ.comp j) '' Cl)) :=
  by
  intro _ _ _ _ _ _ _ _ j hj _ _ _ _ C
  exact ⟨C.pull j hj⟩

end GlobalTheory.BKLim
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.GalPhi

variable {l : ℕ} [Fact l.Prime]

theorem σA_frobenius (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  apply inclW_injective
  rw [← frobW_inclW, ← galW_inclW, ← galW_inclW, ← frobW_inclW]
  refine WittVector.ext fun n => ?_
  simp [galW, frobW, mapAlgEquivW, mapEquivW, WittVector.map_coeff, frobenius_def]

theorem frobenius_algebraMap (z : ℤ_[l]) :
    WittVector.frobenius (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z := by
  change WittVector.frobenius (zlW l (OCb l) z) = zlW l (OCb l) z
  rw [WittVector.frobenius_eq_map_frobenius]
  simp only [zlW, RingHom.comp_apply]
  refine WittVector.ext fun n => ?_
  simp only [WittVector.map_coeff]
  exact congrArg (fun φ : ZMod l →+* OCb l => φ (((WittVector.equiv l).symm.toRingHom z).coeff n))
    (RingHom.ext_zmod ((frobenius (OCb l) l).comp (ZMod.castHom (dvd_refl l) (OCb l))) (ZMod.castHom (dvd_refl l) (OCb l)))

theorem gal_ainf {K : FinExt l} (bk : BK K) (τ : Ainf l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (hY : Y.map (inclW l) = inclW l τ ^ N • F.T)
    (g : ↥(GK K)) :
    τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) =
      Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) := by
  have hz : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW (ρ g) := by
    refine Matrix.ext fun i j => ?_; exact (inclWA l).commutes _
  have hσ : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
    refine Matrix.ext fun i j => ?_; exact (galW_inclW _ _).symm
  have hT : (Y.map (inclW l)).map (galW l (g : GQ l)) = inclW l (Per.σA (g : GQ l) τ) ^ N • F.T.map (galW l (g : GQ l)) := by
    rw [hY, ← galW_inclW, ← map_pow]
    refine Matrix.ext fun i j => ?_; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  refine Matrix.ext fun i j => ?_
  apply inclW_injective
  have key : (τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l)))).map (inclW l) =
      (Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)).map (inclW l) := by
    rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, Matrix.map_mul,
      hz, hσ, hT, Matrix.mul_smul, F.gal, hY, Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
    simp only [map_pow]
  exact congrFun (congrFun key i) j

end GlobalTheory.GalPhi


open GlobalTheory.GalPhi in
theorem GlobalTheory.GalPhi.galPhi : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), (bk.ev bk.E * τ) ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * (Y.map WittVector.frobenius).map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) (bk.ev bk.E * τ) ^ N • (Y.map WittVector.frobenius * (F.ε g).map WittVector.frobenius) := by
  intro l _ K bk τ hτ N d ρ F Y hY g
  have h := congrArg (fun M => M.map (WittVector.frobenius : Ainf l →+* Ainf l)) (gal_ainf bk τ N d ρ F Y hY g)
  rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, Matrix.map_mul,
    map_pow, map_pow, ← σA_frobenius, hτ.1] at h
  have h1 : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (WittVector.frobenius : Ainf l →+* Ainf l) =
      (ρ g).map (algebraMap ℤ_[l] (Ainf l)) := by
    refine Matrix.ext fun i j => ?_; exact frobenius_algebraMap _
  have h2 : (Y.map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l) =
      (Y.map WittVector.frobenius).map (Per.σA (g : GQ l)) := by
    refine Matrix.ext fun i j => ?_; exact (σA_frobenius _ _).symm
  rw [h1, h2] at h
  exact h

end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.AdaptedHodge

variable {l : ℕ} [Fact l.Prime]

theorem xi_unit_fil (C : Core l) (ξ : Ainf l) (hξ : Ideal.span {ξ} = RingHom.ker (Per.θ l)) :
    ∃ u : (Per.BdR l)ˣ, (u : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ∧
      ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a →
        ∃ w : Per.BdRp l, x = ((u ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w := by
  have he := core_isEps l C
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l
  have h1 : xi C.ε ∈ Ideal.span {ξ} := by rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
  have h2 : ξ ∈ Ideal.span {xi C.ε} := by rw [← C.ker_theta, ← hξ]; exact Ideal.mem_span_singleton_self _
  obtain ⟨a0, ha0⟩ := Ideal.mem_span_singleton'.1 h1
  obtain ⟨b0, hb0⟩ := Ideal.mem_span_singleton'.1 h2
  have hX := TiedUnif.isUnit_xi he
  have key : aDp l a0 * aDp l b0 * aDp l (xi C.ε) = aDp l (xi C.ε) := by
    rw [← map_mul, ← map_mul, mul_assoc, hb0, ha0]
  have hab : aDp l a0 * aDp l b0 = 1 := by
    apply hinj
    rw [map_one]
    apply hX.mul_right_cancel
    rw [one_mul, ← map_mul, key]
  have hα : IsUnit (aDp l a0) := IsUnit.of_mul_eq_one _ hab
  have hXe : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi C.ε)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a0) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) := by
    rw [← map_mul, ← map_mul, ha0]
  have hu : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ)) :=
    isUnit_of_mul_isUnit_right (hXe ▸ hX)
  refine ⟨hu.unit, hu.unit_spec, fun a x hx => ?_⟩
  obtain ⟨w, rfl⟩ := (TiedUnif.mem_FilD_iff he a x).1 hx
  have hEq : hX.unit = hu.unit * Units.map (algebraMap (Per.BdRp l) (Per.BdR l) : Per.BdRp l →* Per.BdR l) hα.unit :=
    Units.ext (by simp [hXe, mul_comm])
  refine ⟨((hα.unit ^ a : (Per.BdRp l)ˣ) : Per.BdRp l) * w, ?_⟩
  rw [hEq, mul_zpow, ← map_zpow, Units.val_mul, map_mul, mul_assoc]
  rfl

end GlobalTheory.BKLim.AdaptedHodge

namespace GlobalTheory.BKLim

theorem hodge_of_adapted : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (x : Fin d → Fin d → P.R.BdR) (h : Fin d → ℤ), (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) → (∀ j i, x j i ∈ (P.PD K).Fil (h j)) → (∀ y : Fin d → P.R.BdR, (∀ i, y i ∈ (P.PD K).Fil 0) → ∃ c : Fin d → P.R.BdR, (∀ j, c j ∈ (P.PD K).Fil (-h j)) ∧ y = ∑ j, c j • x j) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ i, (H.p i : ℤ) - H.q = h i := by
  intro l _ K P AI T C hfit ξ hξ d ρ x h hinv hfil hspan
  obtain ⟨u, hu, hF⟩ := AdaptedHodge.xi_unit_fil C ξ hξ
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l
  have hV : ∀ j i, ∃ w : Per.BdRp l, T.eD (x j i) = ((u ^ h j : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w :=
    fun j i => hF _ _ ((T.fil K _ _).1 (hfil j i))
  choose w hw using hV
  have h0 : ∀ i (k : Fin d), (Pi.single i (1 : P.R.BdR) : Fin d → P.R.BdR) k ∈ (P.PD K).Fil 0 := by
    intro i k
    rw [T.fil]
    by_cases hk : k = i
    · subst hk
      rw [Pi.single_eq_same, map_one, ← map_one (algebraMap (Per.BdRp l) (Per.BdR l))]
      exact TiedUnif.alg_mem_FilD_zero 1
    · rw [Pi.single_eq_of_ne hk, map_zero]
      exact zero_mem _
  choose c hc hsum using fun i => hspan (Pi.single i 1) (h0 i)
  have hW : ∀ i j, ∃ w' : Per.BdRp l, T.eD (c i j) = ((u ^ (-h j) : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w' :=
    fun i j => hF _ _ ((T.fil K _ _).1 (hc i j))
  choose w' hw' using hW
  have hq : ∀ j, 0 ≤ h j + ((∑ j, (h j).natAbs : ℕ) : ℤ) := by
    intro j
    have h1 : (h j).natAbs ≤ ∑ j, (h j).natAbs := Finset.single_le_sum (f := fun j => (h j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hcan : ∀ j, ((u ^ (-h j) : (Per.BdR l)ˣ) : Per.BdR l) * ((u ^ h j : (Per.BdR l)ˣ) : Per.BdR l) = 1 := by
    intro j
    rw [← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  have hVW : (Matrix.of fun i j => w j i) * (Matrix.of fun j i => w' i j) = 1 := by
    ext k i
    apply hinj
    have e1 := congrArg (fun y : Fin d → P.R.BdR => T.eD (y k)) (hsum i)

    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at e1

    rw [Matrix.mul_apply, map_sum]
    simp only [Matrix.of_apply, map_mul]
    have e2 : ∀ j, T.eD (c i j) * T.eD (x j k) = algebraMap (Per.BdRp l) (Per.BdR l) (w j k) * algebraMap (Per.BdRp l) (Per.BdR l) (w' i j) := by
      intro j
      rw [hw, hw']
      linear_combination (algebraMap (Per.BdRp l) (Per.BdR l) (w j k) * algebraMap (Per.BdRp l) (Per.BdR l) (w' i j)) * hcan j
    simp only [e2] at e1
    rw [← e1, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  have hz : ∀ z : ℤ_[l], T.eD (algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) =
      ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) (zOm l z) := by
    intro z
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, hfit.o]
    rfl
  refine ⟨{ V := Matrix.of fun i j => w j i
            unit := ⟨⟨_, _, hVW, _root_.mul_eq_one_comm.mp hVW⟩, rfl⟩
            p := fun j => (h j + ((∑ j, (h j).natAbs : ℕ) : ℤ)).toNat
            q := ∑ j, (h j).natAbs
            Q := Matrix.of fun i j => T.eD (x j i)
            Q_eq := ?_
            inv := ?_ }, ?_⟩
  · intro i j
    simp only [Matrix.of_apply]
    rw [hw, map_mul, map_pow, ← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← mul_assoc, ← Units.val_mul,
      ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_add, Int.toNat_of_nonneg (hq j), add_comm]
  · intro g _
    ext i j
    have e1 := congrArg (fun y : Fin d → P.R.BdR => T.eD (y i)) (hinv j g)

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, T.actD, hz] at e1
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact e1
  · intro i
    simp only
    rw [Int.toNat_of_nonneg (hq i)]
    ring

end GlobalTheory.BKLim
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.AdicComplExists

variable {L : Type} [CommRing L] {J : Ideal L}

theorem evalₐ_algebraMap' (n : ℕ) (r : L) :
    AdicCompletion.evalₐ J n (algebraMap L (AdicCompletion J L) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem mem_map_pow_iff (hfg : J.FG) (n : ℕ) (y : AdicCompletion J L) :
    y ∈ (J ^ n).map (algebraMap L (AdicCompletion J L)) ↔ AdicCompletion.evalₐ J n y = 0 := by
  rw [← Submodule.restrictScalars_mem L, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (J ^ n • ⊤ : Ideal L) = J ^ n := by ext x; simp
  exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq L h').injective).symm

end GlobalTheory.BSP.AdicComplExists


open GlobalTheory.BSP.AdicComplExists in
theorem GlobalTheory.BSP.isCompl_exists : ∀ (L : Type) [CommRing L] (J : Ideal L), J.FG →
    ∃ (Q : Type) (_ : CommRing Q) (i : L →+* Q), IsCompl i J := by
  intro L _ J hfg
  refine ⟨AdicCompletion J L, inferInstance, algebraMap L (AdicCompletion J L), ⟨?_, ?_, ?_⟩⟩
  · rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete hfg
  · intro x n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
    exact ⟨r, by rw [mem_map_pow_iff hfg, map_sub, evalₐ_algebraMap', hr, sub_self]⟩
  · intro a n ha
    rw [mem_map_pow_iff hfg, evalₐ_algebraMap'] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

theorem _root_.GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' :
    ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧),
      descN (K := K) p f = X ^ p * (⇑(derivative (R := K)))^[p] f := by
  intro K _ p f
  ext n
  rw [coeff_descN, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative, ← Nat.add_descFactorial_eq_ascFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (Nat.lt_of_not_ge h), Nat.cast_zero, zero_mul]
end
