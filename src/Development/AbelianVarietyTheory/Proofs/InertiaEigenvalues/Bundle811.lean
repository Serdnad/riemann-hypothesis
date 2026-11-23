module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle802
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle217
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle719
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle732
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle651
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle803
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle630
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle759
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.InvBasis

variable {l : ℕ} [Fact l.Prime]

theorem pD_alg_pt : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.AinfP l), Formalism.Per.pD l a = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) a) :=
  GlobalTheory.RingIface.pD_eq_alg

theorem zD_alg_pt : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zD l z = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z))) :=
  GlobalTheory.RingIface.zD_eq_alg

theorem isUnit_gen_pt (l : ℕ) [Fact l.Prime] {a : Per.AinfP l} (h : Per.kerP l = Ideal.span {a}) : IsUnit (Per.pD l a) := GlobalTheory.RingIface.isUnit_of_generator l h

theorem padicInt_hom_ext_pt (f g : ℤ_[l] →+* Per.Ainf l) : f = g := by
  ext1 z
  haveI : IsHausdorff (Ideal.span {((l : ℕ) : Per.Ainf l)}) (Per.Ainf l) := inferInstance
  rw [← sub_eq_zero]
  refine IsHausdorff.haus this _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h := PadicInt.appr_spec n z
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * c := by rw [← hc]; ring
  refine ⟨f c - g c, ?_⟩
  conv_lhs => rw [hz]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

theorem zD_eq_pt (z : ℤ_[l]) :
    algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (algebraMap ℤ_[l] (Ainf l) z)) = Per.zD l z := by
  have h : algebraMap ℤ_[l] (Ainf l) = Per.zA l := padicInt_hom_ext_pt _ _
  rw [h, zD_alg_pt l z, aDp, RingHom.comp_apply]

theorem matrix_map_smul {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (r : R) (M : Matrix (Fin d) (Fin d) R) :
    (r • M).map f = f r • M.map f := by
  ext i j; simp

theorem frob_basis_eq {K : FinExt l} {bk : BK K} {τ : Ainf l} (hτ : bk.IsPer τ) {N d : ℕ}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (hY : Y.map (inclW l) = inclW l τ ^ N • F.T) :
    Y.map WittVector.frobenius = Y * F.A.map bk.ev := by
  have hYij : ∀ i j, inclW l (Y i j) = inclW l τ ^ N * F.T i j := fun i j => by
    simpa using congrFun (congrFun hY i) j
  have hφij : ∀ i j, bk.evW bk.E ^ N * frobW l (F.T i j) = ∑ k, F.T i k * inclW l (bk.ev (F.A k j)) := fun i j => by
    simpa [Matrix.mul_apply, BK.evW] using congrFun (congrFun F.φ i) j
  refine Matrix.ext fun i j => ?_
  apply GlobalTheory.Prism.inclW_injective

  rw [Matrix.map_apply, ← frobW_inclW, hYij, map_mul, map_pow, frobW_inclW, hτ.1, Matrix.mul_apply, map_sum]
  simp_rw [map_mul, hYij]
  calc (inclW l (bk.ev bk.E) * inclW l τ) ^ N * frobW l (F.T i j)
      = inclW l τ ^ N * (bk.evW bk.E ^ N * frobW l (F.T i j)) := by simp only [BK.evW, RingHom.comp_apply]; ring
    _ = _ := by rw [hφij, Finset.mul_sum]; simp only [mul_assoc, Matrix.map_apply]

theorem isUnit_Etau {K : FinExt l} {bk : BK K} {τ : Ainf l} (hτ : bk.IsPer τ) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E * τ))) := by
  rw [map_mul, map_mul]
  refine IsUnit.mul ?_ ?_
  · have hk : Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)} := by
      rw [GlobalTheory.Per.kerQ_eq_map_ker_theta, ← bk.span_ev, Ideal.map_span, Set.image_singleton]
    have hu := isUnit_gen_pt l hk
    rw [pD_alg_pt] at hu
    rw [aDp, RingHom.comp_apply]
    exact hu
  · have h := GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ 1
    rw [pow_one] at h
    exact ((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ h).map _

theorem exists_invariant_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∃ (B : Matrix (Fin d) (Fin d) (Per.BdRp l)) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit B ∧ IsUnit Q ∧ (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) ∧ (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l (bk.ev bk.E * τ)) ^ N • Q = ((Y * F.A.map bk.ev).map (aDp l) * B).map (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q := by
  intro l _ K bk τ hτ C N d ρ F Y hDR hY
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_beta_limit_bdRPlus_deRhamFrame l K bk N d ρ F hDR
  obtain ⟨k1, β1, hβ1, hB1⟩ := hB 1
  have hBu : IsUnit B := GlobalTheory.T.isUnit_bdRPlus_matrix_of_congr_one l K bk d k1 β1 B hβ1.1 hB1
  have hinv := GlobalTheory.T.breuilKisinLatticeFrame_limit_galois_invariant l K bk N d ρ F B hB
  have hφY := frob_basis_eq hτ F Y hY
  have hgal := GlobalTheory.T.frobenius_galois_relation_frame_ainf l K bk τ hτ N d ρ F Y hY
  obtain ⟨v, hv⟩ := isUnit_Etau hτ
  set ι : Per.BdRp l →+* Per.BdR l := algebraMap (Per.BdRp l) (Per.BdR l) with hι
  set j : Ainf l →+* Per.BdR l := ι.comp (aDp l) with hj
  set P : Matrix (Fin d) (Fin d) (Ainf l) := Y.map WittVector.frobenius with hP
  have hjv : j (bk.ev bk.E * τ) = v := hv.symm
  have hM : ((Y * F.A.map bk.ev).map (aDp l) * B).map ι = P.map j * B.map ι := by
    rw [Matrix.map_mul, ← hφY, Matrix.map_map]; rfl
  refine ⟨B, ((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ N • (((Y * F.A.map bk.ev).map (aDp l) * B).map ι), hBu, ?_,
    fun m => ?_, ?_, ?_⟩
  · obtain ⟨Y₀, Y₀', hY₀, hYY⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F.toPre
    have hY0 : Y₀ = Y := Matrix.ext fun i k => GlobalTheory.Prism.inclW_injective (by
      have := congrFun (congrFun (hY₀.trans hY.symm) i) k
      simpa using this)
    rw [hY0] at hYY
    have hPP : P * Y₀'.map WittVector.frobenius = (bk.ev bk.E * τ) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
      rw [hP, ← Matrix.map_mul, hYY, matrix_map_smul, Matrix.map_one _ (map_zero _) (map_one _), map_pow, hτ.1]
    have hPj : P.map j * (Y₀'.map WittVector.frobenius).map j = ((v : Per.BdR l) ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (Per.BdR l)) := by
      rw [← Matrix.map_mul, hPP, matrix_map_smul, Matrix.map_one _ (map_zero _) (map_one _), map_pow, hjv]
    have hPu : IsUnit (P.map j) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      refine Matrix.isUnit_det_of_right_inverse (B := (((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ (2 * N)) • (Y₀'.map WittVector.frobenius).map j) ?_
      rw [Matrix.mul_smul, hPj, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have hMu : IsUnit (P.map j * B.map ι) := hPu.mul (hBu.map (ι.mapMatrix (m := Fin d)))
    rw [hM, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
    exact (((v⁻¹).isUnit.pow N).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).1 hMu)
  · obtain ⟨k, β, -, h⟩ := hB m
    exact ⟨k, β, h⟩
  · rw [← hv, smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  · intro g
    have hσj : ∀ a : Ainf l, Per.σD (g : GQ l) (j a) = j (Per.σA (g : GQ l) a) := fun a => by
      simp only [hj, RingHom.comp_apply, hι, GlobalTheory.MemLoc.ActLaws.σD_alg, GlobalTheory.MemLoc.ActLaws.σDp_aDp]
    have hσι : ∀ b : Per.BdRp l, Per.σD (g : GQ l) (ι b) = ι (Per.σDp (g : GQ l) b) := fun b =>
      GlobalTheory.MemLoc.ActLaws.σD_alg _ b
    set c : Per.BdR l := ((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ N with hc
    set R : Matrix (Fin d) (Fin d) (Per.BdR l) := (ρ g).map (Per.zD l) with hR
    set S : Matrix (Fin d) (Fin d) (Per.BdR l) := (P.map (Per.σA (g : GQ l))).map j with hS
    set T' : Matrix (Fin d) (Fin d) (Per.BdR l) := (B.map (Per.σDp (g : GQ l))).map ι with hT'
    set Ej : Matrix (Fin d) (Fin d) (Per.BdR l) := ((F.ε g).map ((aDp l).comp WittVector.frobenius)).map ι with hEj
    have f1 : (v : Per.BdR l) ^ N • (R * S) = Per.σD (g : GQ l) (v : Per.BdR l) ^ N • (P.map j * Ej) := by
      have h1 := congrArg (fun M => M.map j) (hgal g)
      simp only [matrix_map_smul, Matrix.map_mul, map_pow] at h1
      rw [hjv, ← hσj, hjv] at h1
      have eR : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map j = R := Matrix.ext fun a b => zD_eq_pt (ρ g a b)
      have eE : ((F.ε g).map WittVector.frobenius).map j = Ej := Matrix.ext fun _ _ => rfl
      rw [eR, eE] at h1
      exact h1
    have f2 : Ej * T' = B.map ι := by
      have h2 := congrArg (fun M => M.map ι) (hinv g)
      simpa only [Matrix.map_mul] using h2
    have f3 : (c • (P.map j * B.map ι)).map (Per.σD (g : GQ l)) = Per.σD (g : GQ l) c • (S * T') := by
      rw [matrix_map_smul, Matrix.map_mul]
      congr 2
      · exact Matrix.ext fun a b => by simp only [Matrix.map_apply, hS, hσj]
      · exact Matrix.ext fun a b => by simp only [Matrix.map_apply, hT', hσι]
    have hw : Per.σD (g : GQ l) c * Per.σD (g : GQ l) (v : Per.BdR l) ^ N = 1 := by
      rw [hc, map_pow, ← mul_pow, ← map_mul, Units.inv_mul, map_one, one_pow]
    have key : (v : Per.BdR l) ^ N • (R * (Per.σD (g : GQ l) c • (S * T'))) = P.map j * B.map ι := by
      rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, f1,
        Matrix.smul_mul, smul_smul, Matrix.mul_assoc, f2, hw, one_smul]
    rw [hM, f3]
    calc R * (Per.σD (g : GQ l) c • (S * T')) = (c * (v : Per.BdR l) ^ N) • (R * (Per.σD (g : GQ l) c • (S * T'))) := by
          rw [hc, ← mul_pow, Units.inv_mul, one_pow, one_smul]
      _ = c • (P.map j * B.map ι) := by rw [mul_smul, key]

end GlobalTheory.BKLim.InvBasis

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EvalEx

theorem semiBC_comp {A B C M N P : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P] {f : A →+* B} {g : B →+* C} {k : A →+* C}
    (u : M →ₛₗ[f] N) (t : N →ₛₗ[g] P) (w : M →ₛₗ[k] P) (hk : ∀ a, k a = g (f a)) (hw : ∀ x, w x = t (u x))
    (hu : SemiBC u) (ht : SemiBC t) : SemiBC w := by
  intro Q _ _ v
  letI : Module B Q := Module.compHom Q g
  let v' : M →ₛₗ[f] Q :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun a x => by
        change v (a • x) = g (f a) • v x
        rw [v.map_smulₛₗ, hk] }
  obtain ⟨z, hz, hzu⟩ := hu Q v'
  let z' : N →ₛₗ[g] Q :=
    { toFun := z
      map_add' := z.map_add
      map_smul' := fun b n => z.map_smul b n }
  obtain ⟨y, hy, hyu⟩ := ht Q z'
  refine ⟨y, fun x => by rw [hw, hy]; exact hz x, fun y' hy' => hyu y' fun n => ?_⟩
  let r : N →ₗ[B] Q :=
    { toFun := fun n => y' (t n)
      map_add' := fun n n' => by simp only [map_add (f := _)]
      map_smul' := fun b n => by
        change y' (t (b • n)) = g b • y' (t n)
        rw [t.map_smulₛₗ, y'.map_smul] }
  have := hzu r fun x => by
    change y' (t (u x)) = v x
    rw [← hw]; exact hy' x
  exact LinearMap.congr_fun this n

theorem ε_mulVec {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) {B : Obj l ↥(OL K)}
    (f g h : Hom bk.prism B) (v : Fin d → B.A) :
    (S.ε f g).mulVec ((S.ε g h).mulVec v) = (S.ε f h).mulVec v := by
  rw [Matrix.mulVec_mulVec, S.ε_trans]

theorem hom_comp_assoc {l : ℕ} {R : Type} [CommRing R] {X Y Z W : Obj l R} (p : Hom Z W) (q : Hom Y Z)
    (r : Hom X Y) : (p.comp q).comp r = p.comp (q.comp r) := Hom.ext' rfl

end GlobalTheory.BSP.EvalEx

namespace GlobalTheory.BSP

theorem exists_eval : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B : Obj l ↥(OL K)), ∃ (N : Type) (_ : AddCommGroup N) (_ : Module B.A N), Nonempty (Eval S B N) := by
  intro l _ K bk d S B
  obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  obtain ⟨P, _, _, _, _, u, hu, hcoc⟩ := GlobalTheory.T.exists_finiteProjective_descent_prismCover l K bk d S B C h f hc
  have hv := GlobalTheory.T.stratifiedCoordinates_of_prismCover l K bk d S B C h f hc P u hcoc
  choose vv hvv using hv
  have po : ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q), ∃ (Q₀ : Obj l ↥(OL K)) (a₀ : Hom C Q₀) (h₀ : Hom Q Q₀),
      a₀.comp h = h₀.comp a ∧ Cover h₀ ∧ Function.Injective h₀.f := by
    intro Q a
    obtain ⟨Q₀, a₀, h₀, hpo⟩ := hc.stable.po Q a
    have hc₀ := (GlobalTheory.T.stable_and_cover_prismHom_of_pushout l _ B C Q Q₀ h a a₀ h₀ hpo).2 hc
    exact ⟨Q₀, a₀, h₀, hpo.comm, hc₀, (GlobalTheory.T.prism_cover_injective_and_descent l _ Q Q₀ h₀ hc₀).1⟩
  refine ⟨P, inferInstance, inferInstance, ⟨{
    fin := inferInstance
    proj := inferInstance
    v := fun {Q} a g => vv Q a g
    bc := ?_
    v_ε := ?_
    v_nat := ?_ }⟩⟩
  · intro Q a g
    obtain ⟨Q₀, a₀, h₀, hcomm, hc₀, -⟩ := po Q a
    have hf : ∀ y, a₀.f (h.f y) = h₀.f (a.f y) := fun y => congrArg (fun φ : Hom B Q₀ => φ.f y) hcomm
    have hE1 : S.ε (h₀.comp g) (a₀.comp f) * S.ε (a₀.comp f) (h₀.comp g) = 1 := by
      rw [S.ε_trans, S.ε_refl]
    have hE2 : S.ε (a₀.comp f) (h₀.comp g) * S.ε (h₀.comp g) (a₀.comp f) = 1 := by
      rw [S.ε_trans, S.ε_refl]
    let s : (Fin d → Q₀.A) ≃ₗ[Q₀.A] (Fin d → Q₀.A) :=
      { toFun := (S.ε (h₀.comp g) (a₀.comp f)).mulVec
        invFun := (S.ε (a₀.comp f) (h₀.comp g)).mulVec
        map_add' := Matrix.mulVec_add _
        map_smul' := fun c x => Matrix.mulVec_smul _ c x
        left_inv := fun x => by
          change (S.ε (a₀.comp f) (h₀.comp g)).mulVec ((S.ε (h₀.comp g) (a₀.comp f)).mulVec x) = x
          rw [Matrix.mulVec_mulVec, hE2, Matrix.one_mulVec]
        right_inv := fun x => by
          change (S.ε (h₀.comp g) (a₀.comp f)).mulVec ((S.ε (a₀.comp f) (h₀.comp g)).mulVec x) = x
          rw [Matrix.mulVec_mulVec, hE1, Matrix.one_mulVec] }
    let w0 : P →ₛₗ[h₀.f.comp a.f] (Fin d → Q₀.A) :=
      { toFun := fun x j => a₀.f (u x j)
        map_add' := fun x y => by funext j; simp only [map_add (f := _), Pi.add_apply]
        map_smul' := fun b x => by
          funext j
          simp only [LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.comp_apply, hf] }
    have hw0 : SemiBC w0 := EvalEx.semiBC_comp u (piMap a₀.f (Fin d)) w0 (fun y => (hf y).symm)
      (fun x => rfl) hu (semiBC_piMap a₀.f _)
    exact GlobalTheory.T.semilinear_projective_module_compose l _ Q Q₀ h₀ hc₀ B.A a.f P (Fin d → Q.A) (Fin d → Q₀.A) (vv Q a g)
      (piMap h₀.f (Fin d)) (s.toLinearMap.comp w0) (fun x => (hvv Q a g Q₀ h₀ a₀ hcomm x).symm)
      (semiBC_piMap h₀.f _) (hw0.comp_equiv s)
  · intro Q a g g' x
    obtain ⟨Q₀, a₀, h₀, hcomm, -, hinj⟩ := po Q a
    funext i
    apply hinj
    have e1 := congrFun (hvv Q a g Q₀ h₀ a₀ hcomm x) i
    have e2 := hvv Q a g' Q₀ h₀ a₀ hcomm x
    rw [e1, RingHom.map_mulVec, S.ε_nat,
      show (⇑h₀.f ∘ (vv Q a g') x) = fun i => h₀.f ((vv Q a g') x i) from rfl, e2]
    exact congrFun (EvalEx.ε_mulVec S (h₀.comp g) (h₀.comp g') (a₀.comp f) _).symm i
  · intro Q Q' c a g x i
    have hp := po Q' (c.comp a)
    obtain ⟨Q₁, a₁, h₁, hcomm, -, hinj⟩ := hp
    apply hinj
    have e1 := congrFun (hvv Q' (c.comp a) (c.comp g) Q₁ h₁ a₁ hcomm x) i
    have e2 := congrFun (hvv Q a g Q₁ (h₁.comp c) a₁ (hcomm.trans (EvalEx.hom_comp_assoc h₁ c a).symm) x) i
    have e3 : (h₁.comp c).f ((vv Q a g) x i) = h₁.f (c.f ((vv Q a g) x i)) := rfl
    refine e1.trans (Eq.trans ?_ (e3 ▸ e2).symm)
    exact congrArg (fun φ => (S.ε φ (a₁.comp f)).mulVec (fun j => a₁.f (u x j)) i)
      (EvalEx.hom_comp_assoc h₁ c g).symm

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem frob_coord_compat {C : Type} [CommRing C] {d d' : ℕ} (φ : C →+* C) (E T : C) (hE : E ∈ nonZeroDivisors C)
    (A : Matrix (Fin d) (Fin d) C) (A' : Matrix (Fin d') (Fin d') C) (Y : Matrix (Fin d') (Fin d) C)
    (a a' r r' k j : ℕ) (hY : E ^ a • (A' * Y.map φ) = E ^ a' • (Y * A)) (u m : Fin d → C) (n : Fin d' → C)
    (h1 : T ^ r • (E ^ a • m - T ^ k • A.mulVec fun i => φ (u i)) = 0)
    (h2 : T ^ r' • (E ^ a' • n - T ^ j • A'.mulVec fun i => φ (Y.mulVec u i)) = 0) :
    T ^ (r + r') • (T ^ k • n) = T ^ (r + r') • (T ^ j • Y.mulVec m) := by
  have e1 : (fun i => φ (Y.mulVec u i)) = (Y.map φ).mulVec fun i => φ (u i) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  rw [e1, Matrix.mulVec_mulVec] at h2
  have h3 := congrArg Y.mulVec h1
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mulVec_zero] at h3
  have h4 := congrArg (fun Z => Matrix.mulVec Z fun i => φ (u i)) hY
  simp only [Matrix.smul_mulVec] at h4
  funext i
  have h2i := congrFun h2 i
  have h3i := congrFun h3 i
  have h4i := congrFun h4 i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h2i h3i h4i ⊢
  rw [← sub_eq_zero]
  refine (mem_nonZeroDivisors_iff.1 (pow_mem hE (a + a'))).1 _ ?_
  linear_combination (T ^ r * T ^ k * E ^ a) * h2i - (T ^ r' * T ^ j * E ^ a') * h3i +
    T ^ (r + r' + k + j) * h4i

theorem eval_map_Φ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (M' : FCrys l ↥(OL K)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)), Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)) (V' : Eval S' B (M'.M B)), IsCoord e V → IsCoord e' V' → ∀ w : M.M B →ₗ[B.A] M'.M B, (∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x)) → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → IsFrac (t : B.A) (M'.Φ B t (w x)) (w m) k := by
  intro l _ K bk d d' S S' M e M' e' hF hF' Y hY B V V' hV hV' w hw t x m k hx
  refine (GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B).elim fun C hC => hC.elim fun h hC => hC.1.elim fun g => ?_
  have hc := hC.2
  have hinj := (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' B C (M'.M B) V' h g hc).1
  have hE := (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C g).2
  have hnj : ∃ n j, IsFrac (t : B.A) (M'.Φ B t (w x)) n j := by
    induction M'.Φ B t (w x) using LocalizedModule.induction_on with
    | h n s =>
      obtain ⟨_, j, rfl⟩ := s
      exact ⟨n, j, rfl⟩
  refine hnj.elim fun n hn => hn.elim fun j hn => ?_
  refine (GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d S M e hF B V hV t x m k hx C h g).elim fun r h1 => ?_
  refine (GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d' S' M' e' hF' B V' hV' t (w x) n j hn C h g).elim fun r' h2 => ?_
  rw [hw] at h2
  have hY' : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf g) * (Y.map (BK.hf g)).map C.D.φ) =
      BK.hf g bk.E ^ S'.a • (Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
    have e1 : (Y.map (BK.hf g)).map C.D.φ = (Y.map (frobS l bk.a)).map (BK.hf g) := by
      ext i j
      exact (g.f_φ (Y i j)).symm
    rw [e1, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    have h5 := congrArg (BK.hf g) (congrFun (congrFun hY.φ i) j)
    simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.map_apply] using h5
  have key := frob_coord_compat C.D.φ _ _ hE _ _ _ _ _ _ _ _ _ hY' _ _ _ h1 h2
  unfold IsFrac at hn ⊢
  rw [hn, LocalizedModule.mk_eq]
  refine ⟨⟨(t : B.A) ^ (r + r'), r + r', rfl⟩, hinj ?_⟩
  simp only [Submonoid.smul_def, LinearMap.map_smulₛₗ, map_pow, hw]
  exact key

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.TransLim

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), IsUnit T0 → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∃ Y : ∀ n, Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S, ∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hT0 hR
  have key : ∀ n, ∃ Y : Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S,
      (F n).T * Y.map bk.evW = zW (tw.f n) * (F (n + 1)).T := fun n =>
    GlobalTheory.T.exists_equivariantMap_breuilKisinMatrix l K bk τ hτ N N (tw.d' (n + 1)) (tw.d' n) (fun g => (tw.ρ' (n + 1) g).val)
      (fun g => (tw.ρ' n g).val) (F (n + 1)) (F n) (tw.f n) (tw.f_equi n)
  choose Y hY using key
  refine ⟨Y, fun n => ?_⟩
  let π : WCb l →+* WCb l ⧸ Ideal.span {(l : WCb l) ^ n} := Ideal.Quotient.mk _
  have hz : ∀ {a b : ℕ} (M M' : Matrix (Fin a) (Fin b) (WCb l)),
      (∀ i j, (l : WCb l) ^ n ∣ (M - M') i j) ↔ M.map π = M'.map π := by
    intro a b M M'
    constructor
    · intro h
      ext i j
      simp only [Matrix.map_apply]
      rw [← sub_eq_zero, ← map_sub]
      exact (Ideal.Quotient.eq_zero_iff_dvd _ _).2 (by simpa [Matrix.sub_apply] using h i j)
    · intro h i j
      rw [Matrix.sub_apply]
      refine (Ideal.Quotient.eq_zero_iff_dvd _ _).1 ?_
      rw [map_sub, sub_eq_zero]
      exact congrFun (congrFun h i) j
  have hA : (zW (tw.Pi n)).map π * (F n).T.map π = T0.map π * (R n).map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]; exact (hz _ _).1 (hR n)
  have hD : (zW (tw.Pi (n + 1))).map π * (F (n + 1)).T.map π = T0.map π * (R (n + 1)).map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    refine (hz _ _).1 fun i j => ?_
    exact dvd_trans (pow_dvd_pow _ (Nat.le_succ n)) (hR (n + 1) i j)
  have hB : (F n).T.map π * ((Y n).map bk.evW).map π = (zW (tw.f n)).map π * (F (n + 1)).T.map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hY n]
  have hC : (zW (tw.Pi n)).map π * (zW (tw.f n)).map π = (zW (tw.Pi (n + 1))).map π := by
    rw [← Matrix.map_mul]
    refine (hz _ _).1 fun i j => ?_
    have h1 := map_dvd (algebraMap ℤ_[l] (WCb l)) (tw.f_Pi n i j)
    simp only [map_pow, map_natCast] at h1
    convert h1 using 1

    simp [zW, Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, map_sum, map_mul]
  obtain ⟨u, hu⟩ := hT0
  have hinv : ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * T0.map π = 1 := by
    rw [← Matrix.map_mul, ← hu, Units.inv_mul, Matrix.map_one _ (map_zero π) (map_one π)]
  have hE : T0.map π * ((R n).map π * ((Y n).map bk.evW).map π) = T0.map π * (R (n + 1)).map π := by
    rw [← Matrix.mul_assoc, ← hA, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hC, hD]
  have hF : (R n).map π * ((Y n).map bk.evW).map π = (R (n + 1)).map π := by
    have := congrArg (fun M => ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * M) hE
    simpa only [← Matrix.mul_assoc, hinv, Matrix.one_mul] using this
  rw [← Matrix.map_mul] at hF
  exact (hz _ _).2 hF

end GlobalTheory.BKLim.TransLim
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BKGal.gb_sub_b_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b - b ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hMon b hb g hg
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  refine ⟨C, ?_⟩
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, rfl⟩ := hb
  obtain ⟨b₁, hb₁, hF⟩ := GlobalTheory.T.value_mem_filtration_zero_tame l a e O K t ϖ hl2 ι η H D T R y hyY hy m₀ h1
  have hv : IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) (b₀ - b₁) := by
    rw [← h1]; exact GlobalTheory.BKGal.IsCrisVal.sub t ϖ h4 hb₁
  have h5 := GlobalTheory.T.galois_sub_value_mem_filZero_of_monodromy_zero l a e O K t ϖ hl2 ι η H D T R y hyY hMon hy σ h2 h3 (b₀ - b₁) hv g hg C
  have h6 := hF g hg C
  have h7 := Submodule.sub_mem _ h5 h6
  convert h7 using 1
  simp only [map_sub]
  abel
end
