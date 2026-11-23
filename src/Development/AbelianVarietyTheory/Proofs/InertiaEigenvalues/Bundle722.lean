module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle659
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle705
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle539
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.ExtGood

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l}
  [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l)

abbrev ext (T : QLat LL) (z : ↥(latticeCocycles T.L)) : QLat LL :=
  GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z

theorem aeval_mul_eq_zero {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (A : Module.End K M)
    (p q : Polynomial K) (x : M) (h : Polynomial.aeval A q x = 0) : Polynomial.aeval A (p * q) x = 0 := by
  rw [map_mul, Module.End.mul_apply, h, map_zero]

theorem isGood_mono (T : QLat LL) {Sig : Finset (ZMod e)} {U : Finset ℤ} (h : IsGood a ϖ Pl T {0} {0})
    (hS : (0 : ZMod e) ∈ Sig) (hU : (0 : ℤ) ∈ U) : IsGood a ϖ Pl T Sig U := by
  refine ⟨h.crys, fun g hg w hw x hx => ?_, fun τ j hj => ?_⟩
  · have h1 := h.type g hg w hw x hx
    rw [Finset.prod_singleton] at h1
    rw [← Finset.prod_erase_mul _ _ hS]
    exact aeval_mul_eq_zero _ _ _ _ h1
  · have h2 := h.jumps τ j hj
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at h2
    subst h2
    exact hU

def incl (T : QLat LL) (z : ↥(latticeCocycles T.L)) : LatHom T.L (ext T z).L where
  f := LinearMap.inl ↥LL.1 T.V ↥LL.1
  equiv g x := by
    change ((T.ρ g x, 0) : T.V × ↥LL.1) = (T.ρ g x + (0 : ↥LL.1) • (z : Gl l → T.V) g, 0)
    simp
  cont := continuous_id.prodMk continuous_const
  T_le x hx := ⟨hx, 0, map_zero _⟩

def proj (T : QLat LL) (z : ↥(latticeCocycles T.L)) : LatHom (ext T z).L (unitLat (Gl l) : QLat LL).L where
  f := LinearMap.snd ↥LL.1 T.V ↥LL.1
  equiv g x := rfl
  cont := continuous_snd
  T_le x hx := hx.2

theorem extLat_isGood : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ), (0 : ZMod e) ∈ Sig → (0 : ℤ) ∈ U → IsGood a ϖ Pl (unitLat (Gl l) : QLat LL) Sig U ∧ ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ (Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L) (v : Tp.V), IsSESLat (Qp := ℚ_[l]) f g ∧ v ∈ Tp.L.T ∧ g.f v = (1 : ↥LL.1) ∧ (∀ h, Tp.ρ h v - v = f.f (c h)) ∧ IsGood a ϖ Pl Tp Sig U := by
  intro _ l _ a e _ _ ϖ LL _ _ Pl AI hstd Sig U hS hU
  refine ⟨isGood_mono ϖ Pl _ (UnitModel.isGood_of_trivial ϖ Pl _ fun _ _ => rfl) hS hU, fun T hT c hc => ?_⟩
  let z : ↥(latticeCocycles T.L) := ⟨c, hc.1⟩
  have hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ := hc.2
  have hcr := GlobalTheory.T.crystalline_of_extension_lattice ϖ Pl T hT.crys z hz
  refine ⟨ext T z, incl T z, proj T z, ((0 : T.V), (1 : ↥LL.1)), ⟨LinearMap.inl_injective,
    fun y => ⟨(0, y), rfl⟩, fun y hy => ?_, fun x => ?_, fun y hy => ?_⟩, ⟨zero_mem _, 1, (algebraMap (OL LL) LL.1).map_one⟩, rfl,
    fun h => ?_, ⟨hcr, GlobalTheory.T.tame_type_of_extension_lattice ϖ Pl T Sig hS hT.type z hz, GlobalTheory.T.crystalline_extension_of_jumps ϖ Pl AI hstd T U hU hT.crys hT.jumps z hcr⟩⟩
  · obtain ⟨o, rfl⟩ := hy
    exact ⟨(0, Algebra.linearMap _ _ o), ⟨zero_mem _, o, rfl⟩, rfl⟩
  · change x.2 = 0 ↔ ∃ y, ((y, 0) : T.V × ↥LL.1) = x
    exact ⟨fun h0 => ⟨x.1, Prod.ext rfl h0.symm⟩, fun ⟨y, hy⟩ => by rw [← hy]⟩
  · exact hy.1
  · change ((T.ρ h 0 + (1 : ↥LL.1) • (z : Gl l → T.V) h, (1 : ↥LL.1)) : T.V × ↥LL.1) - (0, 1) = (c h, 0)
    simp only [map_zero, zero_add, one_smul]
    exact Prod.ext (sub_zero _) (sub_self _)

end GlobalTheory.ExtGood
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem repr_map_baseChange {l : ℕ} [Fact l.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] T) (s : WCb l →ₗ[ℤ_[l]] WCb l) (r : T →ₗ[ℤ_[l]] T)
    (y : WCb l ⊗[ℤ_[l]] T) (i : Fin d) :
    (b.baseChange (WCb l)).repr (TensorProduct.map s r y) i =
      ∑ n, algebraMap ℤ_[l] (WCb l) (LinearMap.toMatrix b b r i n) * s ((b.baseChange (WCb l)).repr y n) := by
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul,
      ← congrFun (LinearMap.toMatrix_mulVec_repr b b r t) i, Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Module.Basis.baseChange_repr_tmul, map_smul, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
  | add y z hy hz =>
    rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, hy, hz, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [map_add (f := _), Finsupp.add_apply, mul_add]

end GlobalTheory.BSP

namespace GlobalTheory.BSP



theorem exists_mReal_of_realises : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K M (ainfObj K) (ainfId K) T ρ j → ∃ (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U ∧ ∀ k, j (M.tr bk.ι (e k)) = ∑ i, U i k ⊗ₜ[ℤ_[l]] b i := by
  intro l _ K bk d S M e hF T _ _ ρ j H
  have hfin := H.finite
  have hfree := H.free
  obtain ⟨e', he'⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) (Fin d) e
  obtain ⟨c, hc⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ j H.bc (Fin d) e'
  have hrank : Module.finrank ℤ_[l] T = d := by
    rw [← Module.finrank_baseChange (R := WCb l), Module.finrank_eq_card_basis c, Fintype.card_fin]
  let b := Module.finBasisOfFinrankEq ℤ_[l] T hrank
  let U : Matrix (Fin d) (Fin d) (WCb l) := (b.baseChange (WCb l)).toMatrix c
  have hck : ∀ k, c k = ∑ i, U i k • (b.baseChange (WCb l)) i := fun k => ((b.baseChange (WCb l)).sum_repr (c k)).symm
  have hcj : ∀ k, c k = j (M.tr bk.ι (e k)) := fun k => by rw [hc, he']
  refine ⟨b, U, ⟨?_, ?_, ?_⟩, fun k => ?_⟩
  · letI := (b.baseChange (WCb l)).invertibleToMatrix c
    exact isUnit_of_invertible _
  · have hu : IsUnit (inclW l (bk.ev bk.E)) := isUnit_inclW_of_span bk.span_ev
    let t : ↥(ainfObj K).I := ⟨bk.ι.f bk.E, bk.ι.f_I _ (Ideal.mem_span_singleton_self _)⟩
    have hu' : IsUnit (((inclW l).comp (ainfId K).toRingHom) (t : (ainfObj K).A)) := hu
    have ht0 : (t : (ainfObj K).A) ≠ 0 := fun h => hu'.ne_zero (by rw [h, map_zero])
    have key : ∀ k, inclW l (bk.ev bk.E) ^ S.a • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c k) =
        ∑ i, bk.evW (S.A i k) • c i := by
      intro k
      have hsum : ∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j') = M.tr bk.ι (e k) := by
        simp [Pi.single_apply]
      obtain ⟨m, s, hm⟩ := exists_isFrac (t : (ainfObj K).A)
        (M.Φ (ainfObj K) t (∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j')))
      obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ (ainfObj K) bk.ι t _ m s hm
      replace hm : IsFrac (t : (ainfObj K).A) (M.Φ (ainfObj K) t (M.tr bk.ι (e k))) m s := by
        simpa only [hsum] using hm
      have hj : inclW l (bk.ev bk.E) ^ s • TensorProduct.map (frobW l).toLinearMap LinearMap.id
          (j (M.tr bk.ι (e k))) = j m := H.j_φ t ht0 _ m s hm
      have hφ1 : (fun j' => (ainfObj K).D.φ ((Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j')) =
          (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) :=
        funext fun j' => by
          by_cases h : j' = k
          · subst h; simp
          · simp [Pi.single_apply, h]
      rw [hφ1] at hr
      have hr3 := (j.map_smulₛₗ ((t : (ainfObj K).A) ^ r) _).symm.trans ((congrArg j hr).trans j.map_zero)
      have hur : IsUnit (((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ r)) := by
        rw [map_pow]; exact hu'.pow r
      have hr5 := sub_eq_zero.1 ((j.map_sub _ _).symm.trans (hur.smul_eq_zero.1 hr3))
      have hr7 := (j.map_smulₛₗ _ _).symm.trans (hr5.trans (j.map_smulₛₗ _ _))
      have e1 : ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) = inclW l (bk.ev bk.E) ^ S.a :=
        map_pow _ _ _
      have e2 : ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) = inclW l (bk.ev bk.E) ^ s :=
        map_pow _ _ _
      have hsum2 : j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) =
          ∑ i, bk.evW (S.A i k) • c i := by

        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.map_smulₛₗ, ← hcj, Matrix.mulVec_single_one]
        rfl
      apply (hu.pow s).smul_left_cancel.1
      calc inclW l (bk.ev bk.E) ^ s • (inclW l (bk.ev bk.E) ^ S.a •
              TensorProduct.map (frobW l).toLinearMap LinearMap.id (c k))
          = inclW l (bk.ev bk.E) ^ S.a • (inclW l (bk.ev bk.E) ^ s •
              TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (M.tr bk.ι (e k)))) := by
            rw [hcj, smul_smul, smul_smul, mul_comm]
        _ = inclW l (bk.ev bk.E) ^ S.a • j m := congrArg _ hj
        _ = ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) • j m := congrArg (· • j m) e1.symm
        _ = ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) •
              j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) := hr7
        _ = inclW l (bk.ev bk.E) ^ s • ∑ i, bk.evW (S.A i k) • c i := by rw [e2, hsum2]
    have hev : ∀ x, bk.evW x = inclW l (bk.ev x) := fun _ => rfl
    refine Matrix.ext fun i k => ?_
    have h := congrArg (fun y => (b.baseChange (WCb l)).repr y i) (key k)

    simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
    repr_map_baseChange, LinearMap.toMatrix_id, Matrix.one_apply, smul_eq_mul, apply_ite (algebraMap ℤ_[l] (WCb l)),
    map_one, map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    AlgHom.toLinearMap_apply] at h
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul, hev, U,
      Module.Basis.toMatrix_apply]
    rw [h]
    exact Finset.sum_congr rfl fun x _ => by rw [hev, mul_comm]
  · intro g
    have keyg : ∀ k, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (c k) =
        ∑ i, inclW l (S.ε bk.ι ((ainfHom K g).comp bk.ι) i k) • c i := by
      intro k

      rw [hcj, ← H.j_act_of g (ainfHom K g) (fun _ => rfl), ← M.tr_comp, hF.tr bk.ι ((ainfHom K g).comp bk.ι) k,
      map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, ← hcj]
      rfl
    refine Matrix.ext fun i k => ?_
    have h := congrArg (fun y => (b.baseChange (WCb l)).repr y i) (keyg k)

    simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
    repr_map_baseChange, smul_eq_mul, AlgEquiv.toLinearMap_apply] at h
    simp only [Matrix.mul_apply, Matrix.map_apply, U, Module.Basis.toMatrix_apply, zW]
    rw [h]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  · rw [← hcj, hck]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem mul_comm_of_mul_eq_smul_one {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) (c : R) (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n R)) :
    B * A = c • (1 : Matrix n n R) := by
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have h2 : (B * A - c • (1 : Matrix n n R)) * B = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      sub_self]
  have h3 : B.det • (B * A - c • (1 : Matrix n n R)) = 0 := by
    have := congrArg (· * B.adjugate) h2
    simp only [Matrix.zero_mul] at this
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at this
    exact this
  have h4 : B * A - c • (1 : Matrix n n R) = 0 := by
    ext i j
    have := congrFun (congrFun h3 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this
    simpa using (mul_eq_zero.1 this).resolve_left hdet
  exact sub_eq_zero.1 h4

variable {l : ℕ} [hl : Fact l.Prime]

theorem BK.ρ₀_pos_lt_one {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 ?_⟩
  have : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by positivity
  linarith

theorem BK.frobenius_ev_E_ne_zero {K : FinExt l} (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) :
    WittVector.frobenius (bk.ev bk.E) ≠ 0 := by
  intro h0
  obtain ⟨h1, ε, η, hε, hφ⟩ := hτ
  have hε1 : ε ≠ 1 := by
    rintro rfl
    obtain ⟨-, hu⟩ := hε
    exact hu (by rw [map_one]; simp)
  have hc0 : τ.coeff 0 ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x => WittVector.constantCoeff x) hφ
    change (WittVector.frobenius τ).coeff 0 = _ at h1
    rw [WittVector.coeff_frobenius_charP, h0, zero_pow (Fact.out : l.Prime).ne_zero, map_mul, map_sub, map_one] at h1
    change 0 = WittVector.constantCoeff (η : Ainf l) * ((WittVector.teichmuller l ε).coeff 0 - 1) at h1
    rw [WittVector.teichmuller_coeff_zero] at h1
    have hη : IsUnit (WittVector.constantCoeff (η : Ainf l)) := η.isUnit.map _
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact hη.ne_zero h
    · exact hε1 (sub_eq_zero.1 h)
  have h2 := congrArg WittVector.frobenius h1
  rw [map_mul, h0, zero_mul] at h2
  have h3 := congrArg (fun x : Ainf l => x.coeff 0) h2
  simp only [WittVector.coeff_frobenius_charP, WittVector.zero_coeff] at h3
  exact hc0 (pow_eq_zero_iff (Fact.out : l.Prime).ne_zero |>.1 (pow_eq_zero_iff (Fact.out : l.Prime).ne_zero |>.1 h3))

theorem Seed.crystallineDiscPeriods_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ),
    ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ →
      ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ =
        s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  intro l _ K bk τ hτ d ρ _ s Φ hΦ
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hΦS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x) := fun x => by
    change Φ (bk.iA (bk.ev x)) = bk.iA (bk.ev (frobS l bk.a x))
    rw [hΦ.ext, bk.ev_frob]
  have he : bk.iS (frobS l bk.a bk.E) ≠ 0 := by
    change bk.iA (bk.ev (frobS l bk.a bk.E)) ≠ 0
    rw [bk.ev_frob, ← map_zero bk.iA]
    exact fun h => bk.frobenius_ev_E_ne_zero hτ (hinj h)
  have hL0 : (l : bk.DA bk.ρ₀) ≠ 0 := fun h =>
    WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))
  have hQP : s.X.map (bk.iS.comp (frobS l bk.a)) * s.X'.map (bk.iS.comp (frobS l bk.a)) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast]
  have hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ he)
  have hPQ := mul_comm_of_mul_eq_smul_one _ _ _ hc hQP
  have hA : (s.X'.map bk.iS).map Φ = s.X'.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; congr 1; funext x; exact hΦS x
  have hF : (s.F.map (C : Wq l bk.a →+* bk.S)).map bk.iS = s.F.map (bk.iS.comp C) := by
    rw [Matrix.map_map]; rfl
  have hX : (s.X.map (frobS l bk.a)).map bk.iS = s.X.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; rfl
  have h2 := congrArg (· * s.X.map (bk.iS.comp (frobS l bk.a))) (s.φ Φ hΦ)
  simp only [Matrix.map_mul, hA] at h2
  rw [Matrix.smul_mul, Matrix.mul_assoc (s.W.map Φ), hPQ, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h2
  rw [Matrix.map_mul, Matrix.map_mul, hF, hX]
  refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero s.N he) ?_
  dsimp only
  calc bk.iS (frobS l bk.a bk.E) ^ s.N • (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
        s.W.map Φ)
      = ((l : bk.DA bk.ρ₀) ^ s.c₁ * ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N))) •
        s.W.map Φ := by rw [smul_smul]; congr 1; ring
    _ = _ := h2
    _ = _ := by rw [Matrix.smul_mul]; simp only [Matrix.mul_assoc]

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem ne_one_of_isEps {l : ℕ} [hl : Fact l.Prime] {ε : OCb l} (hε : GlobalTheory.MemLoc.IsEps ε) : ε ≠ 1 := by
  rintro rfl
  exact hε.2 (by simp)

theorem coeff_zero_ne_zero_of_isPer {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) {τ : Ainf l}
    (hτ : bk.IsPer τ) : τ.coeff 0 ≠ 0 := by
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  intro h
  have h1 := congrArg (WittVector.constantCoeff (p := l) (R := OCb l)) hφ
  simp only [map_mul, map_sub, map_one, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
    WittVector.teichmuller_coeff_zero, h] at h1
  rw [zero_pow hl.out.ne_zero] at h1
  have hη : (η : Ainf l).coeff 0 ≠ 0 := by
    have := η.isUnit.map (WittVector.constantCoeff (p := l) (R := OCb l))
    rw [WittVector.constantCoeff_apply] at this
    exact this.ne_zero
  exact mul_ne_zero hη (sub_ne_zero.2 (ne_one_of_isEps hε)) h1.symm

theorem ρ₀_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)
  exact ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos he)⟩

theorem isUnit_inclW_of_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    IsUnit (inclW l τ) ∧ bk.iA τ ≠ 0 ∧ τ ≠ 0 ∧ ∀ g : GQ l, IsUnit (inclW l (Per.σA g τ)) := by
  intro l _ K bk τ hτ
  have h0 := coeff_zero_ne_zero_of_isPer bk hτ
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact h0 (WittVector.zero_coeff _ _ _)
  have hU : IsUnit (inclW l τ) := by
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [inclW, WittVector.map_coeff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 h0
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ (ρ₀_pos_lt_one bk).1 (ρ₀_pos_lt_one bk).2).1
  refine ⟨hU, fun h => hτ0 (hinj (h.trans (map_zero _).symm)), hτ0, fun g => ?_⟩
  rw [← galW_inclW]
  exact hU.map (galW l g)

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem breuilKisinDatum_uniformizer_radius_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨?_, ?_⟩
  · unfold BK.ρ₀
    exact NNReal.rpow_pos (by positivity)
  · unfold BK.ρ₀
    exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
      have : (0:ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by positivity
      linarith)

theorem linDisjoint_disc (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (sA : bk.S →+* A) (ι : Type) (TB : TopBasis sA bk.J ι) (j : bk.DS bk.ρ₀ →+* Disc l (sA X) bk.ρ₀)
    (hj : IsDiscMap (l := _) (u := _) (ρ := _) sA j) (x y : A) (f g : bk.DS bk.ρ₀) (hg : g ≠ 0) (hy : y ≠ 0)
    (h : toDisc l (sA X) bk.ρ₀ x * j g = toDisc l (sA X) bk.ρ₀ y * j f) :
    ∃ δ a : bk.S, δ ≠ 0 ∧ sA δ * x = sA a * y := by
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatum_uniformizer_radius_pos_lt_one bk
  obtain ⟨cD, hc1, hc2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A sA ι TB bk.ρ₀ hρ0 hρ1 j hj
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hH : IsHausdorff bk.J bk.S := inferInstance
  obtain ⟨hz, -⟩ := GlobalTheory.BSP.TopBasis.basic_facts bk.S A sA bk.J ι TB hH
  have hinj : Function.Injective (toDisc l (X : bk.S) bk.ρ₀) :=
    (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk bk.S (RingHom.id _) Unit (TopBasis.self bk.J) bk.ρ₀ hρ0 hρ1).1
  have hmul := GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative l K bk bk.ρ₀ hρ0 hρ1

  have key : ∀ i, g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i x) = f * toDisc l (X : bk.S) bk.ρ₀ (TB.c i y) := by
    intro i
    have e := congrArg (cD i) h
    rw [mul_comm, mul_comm (toDisc l (sA X) bk.ρ₀ y), hc2, hc2, hc1, hc1] at e
    exact e
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, TB.c i₀ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (hz y hc)
  refine ⟨TB.c i₀ y, TB.c i₀ x, hi₀, ?_⟩
  rw [← sub_eq_zero]
  apply hz
  intro i
  rw [map_sub, TB.c_mul, TB.c_mul]
  apply hinj
  rw [map_zero]
  have h0 : g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y * TB.c i x - TB.c i₀ x * TB.c i y) = 0 := by
    rw [map_sub, map_mul, map_mul, mul_sub]
    have e1 := key i
    have e2 := key i₀
    linear_combination (toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y)) * e1 - (toDisc l (X : bk.S) bk.ρ₀ (TB.c i y)) * e2
  have hn := congrArg norm h0
  rw [hmul, norm_zero, mul_eq_zero] at hn
  rcases hn with hn | hn
  · exact absurd (norm_eq_zero.1 hn) hg
  · exact norm_eq_zero.1 hn

end GlobalTheory.BSP
end
