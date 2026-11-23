module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousScale
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle159
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

section Abstract

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

def mulSq (a b : IdF A) (T : C) (y : A.obj T) : sqM a b T →ₗ[R] sqM a b T where
  toFun x := ⟨Ideal.Quotient.mk _ y * x.1, Ideal.mul_mem_left ((a.S T).map (Ideal.Quotient.mk (b.S T))) _ x.2⟩
  map_add' x x' := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (mul_smul_comm _ _ _)

def mulMor (a b c : IdF A) (y : ∀ T : C, A.obj T)
    (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (A.map φ).hom (y T) ∈ c.S T')
    (hc : ∀ (T : C) {v w : A.obj T}, v ∈ c.S T → w ∈ a.S T → v * w ∈ b.S T) :
    CH.Mor (sq a b) (sq a b) (RingHom.id R) where
  G := 𝟭 C
  τ T := mulSq a b T (y T)
  nat {T T'} φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    have key : ∀ w : A.obj T, w ∈ a.S T → Ideal.Quotient.mk (b.S T') (y T') * Ideal.Quotient.mk (b.S T') ((A.map φ).hom w) =
        Ideal.Quotient.mk (b.S T') ((A.map φ).hom (y T * w)) := by
      intro w hw
      rw [← map_mul, map_mul (A.map φ).hom, Ideal.Quotient.eq, ← sub_mul]
      exact hc _ (hy φ) (a.map_mem φ hw)
    exact Subtype.ext (key w hw)

end Abstract

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem sub_mem_of_lift {W : X.Opens} {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') (f : Γ(X, W))
    (v : T.B) (v' : T'.B) (hv : Ideal.Quotient.mk T.J v = ev T h f) (hv' : Ideal.Quotient.mk T'.J v' = ev T' h' f) :
    v' - φ.φ v ∈ T'.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [hv', ev_nat φ h h', ← hv]
  rfl

theorem lft_mul_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f g : Γ(X, W)) :
    lft W T f * lft W T g - lft W T (f * g) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, lft_spec T h, lft_spec T h, lft_spec T h, map_mul]

theorem J_mul_sFil (P : ObjectProperty (Thick (LL q))) (r : ℕ) (T : P.FullSubcategory) {v w : (sP P).A.obj T}
    (hv : v ∈ (sP P).J.S T) (hw : w ∈ (sFil P r).S T) : v * w ∈ (sFil P ((r : ℤ) + 1)).S T := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have h1 : v ∈ (sFil P 1).S T := by
    have e := hF.one T
    rw [e]
    exact hv
  have := hF.mul 1 r T (x := v) (y := w) h1 hw
  have e : (((1 + r : ℕ)) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
  rwa [e] at this

def mulZ {W : X.Opens} (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (z : Γ(X, W)) :
    CH.Mor (sq (sFil P r) (sFil P ((r : ℤ) + 1))) (sq (sFil P r) (sFil P ((r : ℤ) + 1))) (RingHom.id O) :=
  mulMor (sFil P r) (sFil P ((r : ℤ) + 1)) (sP P).J (fun T => lft W T.obj z)
    (fun {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) z _ _
      (lft_spec _ (hP _ T.property) z) (lft_spec _ (hP _ T'.property) z))
    (fun T _ _ hv hw => J_mul_sFil P r T hv hw)

theorem units_mul_relation_rearrange_commRing {S : Type} [CommRing S] (y w l l' : S) : y * (w * l) - w * l' = (y * l - l') * w := by ring

theorem stAct : StAct := by
  intro O _ X q W P hP r z
  refine ⟨((mulZ P hP r z).pull r).toAddMonoidHom, ?_⟩
  intro d t u hu x c hc
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(mulZ P hP r z).pullC r f, ?_, rfl, ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · intro s
    have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
    let uu : Fin d → ∀ T : P.FullSubcategory, (sP P).A.obj T := fun i T => u i T.obj
    have hl : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'), uu i T' - ((sP P).A.map φ).hom (uu i T) ∈ (sP P).J.S T' :=
      fun i {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) (t i) _ _
        (hu i _ (hP _ T.property)) (hu i _ (hP _ T'.property))
    change Ideal.Quotient.mk _ (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj z) *
      (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f s).1 = _
    rw [hfs s, ← map_mul, Ideal.Quotient.eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have hw := wz_mem hF uu hl I.1 s
    have hd := lft_mul_sub _ (hP _ (s.obj (Fin.last r)).property) z (x I)
    have := J_mul_sFil P r _ hd hw
    have e := units_mul_relation_rearrange_commRing (S := (sP P).A.obj (s.obj (Fin.last r)))
      (lft W (s.obj (Fin.last r)).obj z) (wz uu I.1 s) (lft W (s.obj (Fin.last r)).obj (x I))
      (lft W (s.obj (Fin.last r)).obj (z * x I))
    exact Eq.mpr (congrArg (fun v => v ∈ (sFil P ((r : ℤ) + 1)).S (s.obj (Fin.last r))) e) this

end GlobalTheory.CompanionTheory.GrForm
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lift_sub_mem {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hP : ∀ T, P T → InU W T) (f : Γ(X, W))
    (v : ∀ T : Thick (LL q), T.B) (hv : ∀ (T : Thick (LL q)) (h : InU W T), Ideal.Quotient.mk T.J (v T) = ev T h f)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from v T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from v T.obj) ∈ (sP P).J.S T' := by
  have h := hP _ T.property
  have h' := hP _ T'.property
  change v T'.obj - φ.hom.φ (v T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq, hv _ h', ev_nat φ.hom h h' f, ← hv _ h]
  rfl

theorem exists_of_cocycle : StCocycle → StExists := by
  intro hC O _ X q W d t u hu P hP r x
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hu' : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' :=
    fun i _ _ φ => lift_sub_mem hP (t i) (u i) (hu i) φ
  have hy : ∀ (I : Idx r d) {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from lft W T'.obj (x I)) -
        ((sP P).A.map φ).hom (show (sP P).A.obj T from lft W T.obj (x I)) ∈ (sP P).J.S T' :=
    fun I _ _ φ => lift_sub_mem hP (x I) (fun T => lft W T (x I)) (fun T h => lft_spec T h (x I)) φ
  choose f hf hz using fun I : Idx r d =>
    hC hF (fun i (T : P.FullSubcategory) => (show (sP P).A.obj T from u i T.obj)) hu'
      (fun T : P.FullSubcategory => (show (sP P).A.obj T from lft W T.obj (x I))) (hy I) I.1
  have hd : CH.d (sq (sFil P r) (sFil P ((r : ℤ) + 1))) r (∑ I, f I) = 0 := by

    rw [map_sum]
    exact Finset.sum_eq_zero fun I _ => hf I
  refine ⟨(CH.cx (sq (sFil P r) (sFil P ((r : ℤ) + 1)))).cls (∑ I, f I) hd, ∑ I, f I, hd, rfl, ?_⟩
  intro s
  have e : (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from (∑ I, f I) s) =
      ∑ I, (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f I s) := Finset.sum_apply _ _ _

  rw [e, AddSubmonoidClass.coe_finsetSum, map_sum]
  exact Finset.sum_congr rfl fun I _ => hz I s

end GlobalTheory.CompanionTheory.GrForm
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lift_cocycle_mem {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) {Q : ObjectProperty (Thick (LL q))} (hQ : ∀ T, Q T → InU W T) (i : Fin d)
    {T T' : Q.FullSubcategory} (φ : T ⟶ T') :
    (show (sP Q).A.obj T' from u i T'.obj) - ((sP Q).A.map φ).hom (show (sP Q).A.obj T from u i T.obj) ∈ (sP Q).J.S T' := by
  have h := hQ _ T.property
  have h' := hQ _ T'.property
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  refine Ideal.Quotient.eq.1 ?_
  rw [hu i T'.obj h', ev_nat φ.hom h h' (t i), ← hu i T.obj h]
  rfl

theorem lft_res_sub_mem {W W' : X.Opens} (hW : W' ≤ W) (T : Thick (LL q)) (h : InU W T) (h' : InU W' T) (f : Γ(X, W)) :
    lft W T f - lft W' T (rs hW f) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [lft_spec T h f, lft_spec T h' (rs hW f), ev_res hW T h h' f]

theorem stRes : StRes := by
  intro O _ X q W W' hW d t u hu P P' hPP hP hP' r x c hc
  obtain ⟨f, hf, rfl, hz⟩ := hc
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P'
  have hP'W : ∀ T, P' T → InU W T := fun T h => hP T (hPP T h)
  refine ⟨(resU (GF q r) hPP).pullC r f, ?_, rfl, ?_⟩
  · have := (resU (GF q r) hPP).d_pullC r f
    refine this.trans ?_
    have hf' : CH.d (P.ι ⋙ GF q r) r f = 0 := hf
    rw [hf', map_zero]
  · intro s
    refine (hz (s ⋙ ObjectProperty.ιOfLE hPP)).trans ?_
    refine Ideal.Quotient.eq.2 ?_
    have hdiff : ∀ I : Idx r d,
        wz (Φ := sP P') (fun i T => u i T.obj) I.1 s *
          ((show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) -
            (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I)))) ∈
          (sFil P' ((r : ℤ) + 1)).S (s.obj (Fin.last r)) := by
      intro I
      have hw := wz_mem hF (fun i T => u i T.obj)
        (fun i {T T'} φ => lift_cocycle_mem hu hP'W i φ) I.1 s
      have hδ : (show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) -
          (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I))) ∈
          (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) := by
        have e : (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) = (sP P').J.S (s.obj (Fin.last r)) := hF.one _
        rw [e]
        exact lft_res_sub_mem hW _ (hP'W _ (s.obj (Fin.last r)).property) (hP' _ (s.obj (Fin.last r)).property) (x I)
      have := hF.mul r 1 _ hw hδ
      simpa using this
    have hsum := Ideal.sum_mem _ (t := Finset.univ) (fun I _ => hdiff I)
    simp only [mul_sub, Finset.sum_sub_distrib] at hsum
    exact hsum

end GlobalTheory.CompanionTheory.GrForm
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrFormSmul
open GlobalTheory.CompanionTheory.GrForm

theorem rep_smul {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j} (r : R)
    (h : Rep a b z c) (hz : ∀ s, z' s - r • z s ∈ b.S _) : Rep a b z' (r • c) := by
  obtain ⟨f, hf, rfl, hfz⟩ := h
  refine ⟨r • f, by rw [map_smul, hf, smul_zero], rfl, fun s => ?_⟩
  rw [Ideal.Quotient.eq.mpr (hz s), ← Ideal.Quotient.mkₐ_eq_mk R, map_smul, Ideal.Quotient.mkₐ_eq_mk, ← hfz s]
  rfl

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lft_str_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (a : O) (f : Γ(X, W)) :
    lft W T (strV q W a * f) - T.i a * lft W T f ∈ T.J := by
  rw [← Ideal.Quotient.eq, lft_spec T h, map_mul, map_mul, lft_spec T h, ev_str T h]

theorem lift_nat {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (i : Fin d) {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') :
    u i T' - φ.φ (u i T) ∈ T'.J := by
  rw [← Ideal.Quotient.eq, hu i T' h', ev_nat φ h h', ← hu i T h, Ideal.quotientMap_mk]

private theorem mul_mem_sFil_succ_of_mem_sFil_of_mem_J {P : ObjectProperty (Thick (LL q))} {r : ℕ} (T : P.FullSubcategory)
    {y z : T.obj.B} (hy : y ∈ (sFil P (r : ℤ)).S T) (hz : z ∈ T.obj.J) :
    y * z ∈ (sFil P ((r : ℤ) + 1)).S T := by
  have h1 : z ∈ pdP T.obj.δ 1 := by
    have := GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP T.obj.δ 1 hz
    rwa [T.obj.δ.dpow_one hz] at this
  exact GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.obj.δ r 1 (Ideal.mul_mem_mul (show y ∈ pdP T.obj.δ r from hy) h1)

theorem stSmul : StSmul := by
  intro O _ X q W d t u hu P hP r x c a hc
  unfold Rp at hc ⊢
  refine rep_smul _ _ a hc (fun s => ?_)
  have hw : ∀ I : Fin r → Fin d, wz (Φ := sP P) (fun i T => u i T.obj) I s ∈ (sFil P (r : ℤ)).S (s.obj (Fin.last r)) :=
    fun I => wz_mem (GlobalTheory.CompanionTheory.DPFil.isFil_sFil P) _
      (fun i T T' φ => lift_nat hu i (P.ι.map φ) (hP _ T.property) (hP _ T'.property)) I s
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ (fun I _ => ?_)
  rw [← mul_smul_comm, ← mul_sub]
  exact mul_mem_sFil_succ_of_mem_sFil_of_mem_J _ (hw _) (lft_str_sub _ (hP _ (s.obj (Fin.last r)).property) a (x I))

end GlobalTheory.CompanionTheory.GrFormSmul
end

section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HaarScale

theorem scaleInf : PositivityTheory.PfSWUS.SchInf.ScaleInf := by
  intro F E _ _ _ _ _ σ hσ n M μ ν hμ hν
  classical
  have hR : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨A, hA, hAf⟩ := exists_scale_tuples σ hσ (Ainf F) hR n M μ hμ
  obtain ⟨B, hB, hBf⟩ := exists_scale_herm σ hσ (Ainf F) hR n ν hν
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, hsig, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI := iB n M
  haveI := iTR
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := jB
  haveI := jT2
  have hs : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  refine ⟨A, B, hA, hB, fun g hg => ?_⟩
  have hTc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [rmul]
    exact continuous_finsetSum _ fun c _ => ((continuous_apply_apply c i).mul continuous_const)
  have hTm : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := hTc.measurable
  let τ₀ : HermR (Ainf F) σ n → HermR (Ainf F) σ n := fun S =>
    ⟨conjT (Ainf F) σ g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g, conj_mem (Ainf F) hs _ S⟩
  have hτ₀c : Continuous τ₀ := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have hcT : ∀ S : HermR (Ainf F) σ n, ((τ₀ S : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
      cT (sigR (Ainf F) σ) g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g := fun S => rfl
  have hB0 := hBf g hg τ₀ (fun S => rfl)
  refine ⟨?_, ?_, hAf g hg, fun τ hτ => ?_⟩
  · intro h0
    have h1 := hAf g hg
    rw [h0, zero_smul, Measure.map_eq_zero_iff hTm.aemeasurable] at h1
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := μ)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [h1]; simp)
  · intro h0
    rw [h0, zero_smul, Measure.map_eq_zero_iff hτ₀c.measurable.aemeasurable] at hB0
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := ν)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [hB0]; simp)
  · have : τ = τ₀ := funext fun S => Subtype.ext ((hτ S).trans (hcT S).symm)
    rw [this]
    exact hB0

end GlobalTheory.CompanionTheory.SW.HaarScale
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.serre_class_of_cech_spectral_sequence : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T) (𝒮 : Serre.{1} R) (n : ℕ),
    (∀ p q, p + q = n → 𝒮.P ((cechH F U q).cx.H p)) → 𝒮.P (CH.H F n) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.serre_cech | exact GlobalTheory.CompanionTheory.CechSerre.serre_cech | (intros; apply GlobalTheory.CompanionTheory.CechSerre.serre_cech <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LecShift

theorem leC_shift : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := by
  intro O A _ _ _ I γ X q l s 𝒱 i a ha r T x hx
  have hx' : (show T.obj.B from x) ∈ pdP T.obj.δ (r - i).toNat := hx
  have h1 : T.obj.i a ∈ pdP T.obj.δ i := dividedPowerFiltration_map T.obj.compat i ha
  have h2 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.obj.δ i (r - i).toNat (Ideal.mul_mem_mul h1 hx')
  exact T.obj.pdPow_anti (show r.toNat ≤ i + (r - i).toNat by omega) h2

end GlobalTheory.CompanionTheory.LecShift
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

theorem jacSpan_le_jacS : ∀ {K : Type} [Field K] {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) [Algebra K Γ(X, V)]
    (B : Subalgebra K Γ(X, V)), (B : Set Γ(X, V)) = Set.range (rs h) →
    ∀ {d m : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)) (κ : Fin m → Fin d),
    jacSpan h (RingHom.id _) (fun k => D k) κ ≤ jacS B D κ := by
  intro K _ X V W h _ B hB d m D κ
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨b, bs, rfl⟩
  have hm : ∀ c : Γ(X, W), rs h c ∈ B := fun c => by
    have : rs h c ∈ (B : Set Γ(X, V)) := hB ▸ Set.mem_range_self c
    exact this
  exact AddSubgroup.subset_closure ⟨⟨rs h b, hm b⟩, fun l => ⟨rs h (bs l), hm (bs l)⟩, rfl⟩

end GlobalTheory.CompanionTheory.Cone
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cone_lift_ratio_mem_ideal : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (σ : ComposableArrows C 2), ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1) ∈ (g.obj (σ.obj (Fin.last 2))).J := by
  first | exact @GlobalTheory.CompanionTheory.ConeUnit.r_sub_one | exact GlobalTheory.CompanionTheory.ConeUnit.r_sub_one | (intros; apply GlobalTheory.CompanionTheory.ConeUnit.r_sub_one <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.homogeneous_ideal_component_mem : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  first | exact @GlobalTheory.CompanionTheory.Geo.homIdeal_homog | exact GlobalTheory.CompanionTheory.Geo.homIdeal_homog | (intros; apply GlobalTheory.CompanionTheory.Geo.homIdeal_homog <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.homogeneous_ideal_ne_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), Nonempty X → homIdeal i ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top | exact GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top | (intros; apply GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.basic_open_nonempty_of_ne_zero : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsIntegral X → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}, 0 < e → ∀ (hg : g ∈ grK K N e), Ideal.Quotient.mk (homIdeal i) g ≠ 0 → ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero | exact GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Geo.preimage_basicOpen_nonempty_of_mk_ne_zero <;> assumption)
end
