module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorsCrd

theorem exists_unit_smul {O C J : Type} [CommRing O] [Field C] [Fintype J] [DecidableEq J] (φ : O →+* C)
    (hφ : Function.Injective φ) (m : Matrix J J O) (hm : IsUnit m.det) (w u : J → O) (lam : C)
    (h : ∀ i, φ (u i) = lam * φ (m.mulVec w i)) {i k : J} (hi : IsUnit (w i)) (hk : IsUnit (u k)) :
    ∃ mu : Oˣ, m.mulVec (fun j => (mu : O) * w j) = u := by
  have h1 : φ (m⁻¹.mulVec u i) = lam * φ (w i) := by
    have e : m⁻¹.mulVec (m.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hm, Matrix.one_mulVec]
    conv_rhs => rw [← e]

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h ⊢
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h j]; ring
  obtain ⟨v, hv⟩ := hi.exists_right_inv
  have h2 : φ (m⁻¹.mulVec u i * v) = lam := by
    rw [map_mul, h1, _root_.mul_assoc, ← map_mul, hv, map_one, _root_.mul_one]
  have h3 : ∀ j, u j = (m⁻¹.mulVec u i * v) * m.mulVec w j := fun j => hφ (by rw [map_mul, h2, h])
  have h4 : IsUnit (m⁻¹.mulVec u i * v) := isUnit_of_mul_isUnit_left (h3 k ▸ hk)
  refine ⟨h4.unit, funext fun j => ?_⟩
  rw [h3 j, IsUnit.unit_spec]
  exact congrFun (Matrix.mulVec_smul m (m⁻¹.mulVec u i * v) w) j

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem sec_mem (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} {z : M.Z} (hz : z ∈ Q.W l)
    {x₀ h : S.Gam} (hx : x₀ ∈ S.supI M z) (hh : h ∈ S.HH M z) (i : S.J) :
    (Q.B l i ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z := by
  refine (hB.sec z x₀ hx h hh).1 _ ?_
  rw [Q.basis l z hz]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem sec_unit (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} {z : M.Z} (hz : z ∈ Q.W l)
    {x₀ h : S.Gam} (hx : x₀ ∈ S.supI M z) (hh : h ∈ S.HH M z) :
    ∃ i, IsUnit (⟨_, sec_mem hB Q hz hx hh i⟩ : M.O z) := by
  obtain ⟨h1, i, h2, h3⟩ := hB.sec z x₀ hx h hh
  set v : S.J → Ω := fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i) with hv
  have hvE : v ∈ EE.E z := by
    have e : v = ∑ j, (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i)) • (Pi.single j (1 : Ω) : S.J → Ω) := by
      ext j
      simp [hv, Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def, Algebra.algebraMap_eq_smul_one]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hB.mem z j)
  have hu : IsUnit (⟨_, h1 v hvE⟩ : M.O z) :=
    (RatModel.isUnit_O_iff _).2 ⟨div_ne_zero h2 hx.1, by simpa using h3⟩
  have hvE' := hvE
  rw [Q.basis l z hz] at hvE'
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun k j => Q.B l k j)).1 hvE'
  have e : (⟨_, h1 v hvE⟩ : M.O z) = ∑ k, c k * ⟨_, sec_mem hB Q hz hx hh k⟩ := by
    refine Subtype.ext ?_
    show v ⬝ᵥ S.ev h / S.th x₀ = _
    rw [← hc, sum_dotProduct, Finset.sum_div]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_dotProduct, Subalgebra.smul_def, smul_eq_mul, mul_div_assoc]
  rw [e] at hu
  by_contra hn
  push_neg at hn
  refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_) hu
  exact (IsLocalRing.mem_maximalIdeal _).2 (hn k)

variable {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}

theorem cen {Q : Clos ρ M U₀ EE} {u : ρ.UTest p y₀} (c : Q.Fac y u) : M.Cen U₀ (y (cPt p)) y := by
  refine ⟨rfl, ?_⟩
  have e : gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have e2 : gPt p ≫ y = (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ c.yK) ≫ U₀.ι := by
    rw [Category.assoc, c.yK_fac, ← Category.assoc, ← e, Category.assoc, c.fac]
  rw [e2]
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact ((spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ c.yK) w).2

theorem val_gen (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} (hz : y (cPt p) ∈ Q.W l)
    (hc : M.Cen U₀ (y (cPt p)) y) (ha : S.At M y y₀) {x₀ : S.Gam} (hx : S.th x₀ ≠ 0) (h : S.Gam) (i : S.J) :
    M.val (gPt p ≫ y) ((Q.B l i ⬝ᵥ S.ev h) / S.th x₀) = M.val (gPt p ≫ y) (S.th x₀)⁻¹ *
      ((Q.B l).map (M.val (gPt p ≫ y))).mulVec (fun j => y₀ ⟨S.ev h j, S.ev_mem h j⟩) i := by
  let s : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  set ξ := (gPt p ≫ y) s with hξ
  have hr : Set.range (gPt p ≫ y) = {ξ} := RatModel.range_eq_singleton _ s
  have hU : ξ ∈ U₀ := hc.2 ⟨s, rfl⟩
  have hW : ξ ∈ Q.W l := (RatModel.gPt_specializes rfl s).mem_open (Q.W l).isOpen hz
  have hBm : ∀ j, Q.B l i j ∈ M.O ξ := by
    have : Q.B l i ∈ EE.E ξ := by
      rw [Q.basis l ξ hW]
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [hB.ee.1 ξ hU] at this
    exact (RatModel.Lat.mem_const_iff M).1 this
  have hev : ∀ j, S.ev h j ∈ M.O ξ := fun j => RatModel.mem_ringOn.1 (hB.ov.le (S.ev_mem h j)) ξ hU
  have hth : (S.th x₀)⁻¹ ∈ M.O ξ := RatModel.mem_ringOn.1 (hB.ov.th_unit x₀ hx) ξ hU
  let e : M.O ξ := ⟨_, hth⟩ * ∑ j, ⟨_, hBm j⟩ * ⟨_, hev j⟩
  have he : (Q.B l i ⬝ᵥ S.ev h) / S.th x₀ = (e : Ω) := by
    simp only [e]
    push_cast
    rw [div_eq_inv_mul]
    rfl
  rw [he, ← RatModel.valHom_apply _ _ hr]

  simp only [e, map_mul, map_sum, RatModel.valHom_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (_ * ·) (ha ⟨_, S.ev_mem h j⟩).symm

theorem ker_eq (t : ρ.GeoTest p y₀) : t.τ.yy.ker = t.l.yy.ker := by
  obtain ⟨e, -, he⟩ := t.mt
  ext a
  have := he a 0
  rw [map_zero] at this
  exact this

theorem big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  rw [ρ.N_eq]
  nlinarith

theorem crd_red (hL : GlobalTheory.UT.LL) [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) {Q : Clos ρ M U₀ EE}
    {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c) (hS : S.Big) {x₀ a : S.Gam}
    (hx : x₀ ∈ S.supI M (y (cPt p))) (ha : a ∈ S.HH M (y (cPt p))) (cc : Sp (OO p) ⟶ t.u.G.left) (a' : t.u.PtC)
    (x : t.mod.Φ.Pt) (h₁ : cc ≫ t.u.G.hom = spMap t.u.j) (h₂ : gPt p ≫ cc = t.u.toG a')
    (h₃ : t.u.toA a' = spMap y₀ ≫ (ρ.pt a).left) (h₄ : rPt p ≫ cc = x.left ≫ t.mod.r) :
    ∃ w, Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧
      (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w =
        fun i => M.val (rPt p ≫ y) ((Q.B tm.l i ⬝ᵥ S.ev a) / S.th x₀) := by
  have hv := (GlobalTheory.T.torsionValues_coords_operator_permute hL o Ω S ρ).1 _ y₀ a
  rw [← h₃] at hv
  have hb := t.link a' _ hv
  obtain ⟨wc, hwc⟩ := CrdCalc.crd_exists t.mod.isLB t.σ cc
  have hg := CrdCalc.crd_map (OO p).subtype hwc
  rw [← h₂] at hb
  obtain ⟨κ, hκ⟩ := CrdCalc.crd_unique hg hb
  obtain ⟨⟨i, -, hi⟩, -⟩ := GlobalTheory.T.exists_unit_weightZero_integral_coords hL.1 hL.2.1 p t.u.V t.u.j t.u.G S.g S.N (S.r * S.N) _ t.l.q _ S.J t.σ t.cls
    t.mod (big ρ hS) cc wc h₁ hwc
  obtain ⟨k, hk⟩ := sec_unit hB Q tm.mem hx ha
  let u : S.J → OO p := fun i => RatModel.valLoc y (y (cPt p)) specializes_rfl ⟨_, sec_mem hB Q tm.mem hx ha i⟩
  have hm : IsUnit (tm.m.map t.u.j).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact tm.unit.map _
  obtain ⟨mu, hmu⟩ := exists_unit_smul (OO p).subtype Subtype.val_injective (tm.m.map t.u.j) hm wc u
    (M.val (gPt p ≫ y) (S.th x₀)⁻¹ * κ) (fun i => by
      refine (RatModel.val_spMap_comp (OO p).subtype y specializes_rfl _).symm.trans ?_
      refine (val_gen hB Q tm.mem (cen c) c.at_ hx.1 a i).trans ?_
      rw [tm.m_eq, ← Matrix.mulVec_mulVec, funext hκ, _root_.mul_assoc]
      congr 1

      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact mul_left_comm _ _ _) hi (hk.map _)
  have hr := CrdCalc.crd_map (IsLocalRing.residue (OO p)) (CrdCalc.crd_smul mu hwc)
  obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (t.mod.Φ.H_isLB 1) t.mod.F (R := kb p) x.left
  have hw'' := t.mod.red x w' hw'
  rw [← h₄] at hw''
  obtain ⟨ν, hν⟩ := CrdCalc.crd_unique hw'' hr
  refine ⟨fun j => IsLocalRing.residue (OO p) (mu * wc j), ?_, funext fun i => ?_⟩
  · rw [funext hν]
    exact CrdCalc.crd_smul ν hw'
  · refine Eq.trans ?_ (RatModel.val_spMap_comp (IsLocalRing.residue (OO p)) y specializes_rfl
      ⟨_, sec_mem hB Q tm.mem hx ha i⟩).symm
    refine Eq.trans ?_ (congrArg (IsLocalRing.residue (OO p)) (congrFun hmu i))

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem tors_crd : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → (∀ x : t.mod.Φ.Pt, x ^ (S.r * S.N) = 1 → ∃ w, Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w ∈ Q.Tors (rPt p ≫ y) tm.l) ∧ ∀ v ∈ Q.Tors (rPt p ≫ y) tm.l, ∃ (x : t.mod.Φ.Pt) (w : S.J → kb p), x ^ (S.r * S.N) = 1 ∧ Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w = v := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [c.at_]
    exact RatModel.norm_val_le_one rfl ((M.O _).algebraMap_mem a)
  have hH : S.HH M (y (cPt p)) = t.l.yy.ker := (hB.atTest _ p y y₀ t.τ (cen c) c.at_).trans (ker_eq t)
  obtain ⟨-, g₁, g₂⟩ := GlobalTheory.T.specialFibre_torsion_eq_reductions hL o Ω S ρ p y₀ t.u t.l t.σ t.cls t.mod hint
  have hr : Set.range (rPt p ≫ y) = {y (cPt p)} := by
    rw [RatModel.range_eq_singleton (K := kb p) _ (IsLocalRing.closedPoint (kb p))]
    exact congrArg (fun s => ({y s} : Set M.Z)) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))
  constructor
  · intro x hx
    obtain ⟨a, ha, cc, a', h₁, h₂, h₃, h₄⟩ := g₁ x hx
    obtain ⟨x₀, hx₀⟩ := hB.ov.div (y (cPt p))
    rw [← hH] at ha
    obtain ⟨w, hw, e⟩ := crd_red hL hB tm hS hx₀ ha cc a' x h₁ h₂ h₃ h₄
    exact ⟨w, hw, y (cPt p), by rw [hr]; rfl, x₀, hx₀, a, ha, e⟩
  · rintro v ⟨z, hz, x₀, hx₀, a, ha, rfl⟩
    rw [hr] at hz
    obtain rfl : z = y (cPt p) := hz
    obtain ⟨cc, a', x, h₁, h₂, h₃, h₄, h₅⟩ := g₂ a (hH ▸ ha)
    obtain ⟨w, hw, e⟩ := crd_red hL hB tm hS hx₀ ha cc a' x h₁ h₂ h₃ h₄
    exact ⟨x, w, h₅, hw, e⟩

end GlobalTheory.ZH.TorsCrd
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem GlobalTheory.ZH.exists_geoTest_tMap_and_centre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), Set.range (gPt p ≫ y) ⊆ U₀ → ∃ (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u), Nonempty (Q.TMap t c)) ∧ ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y := by
  intro hL o Ω _ _ _ hA S ρ M U₀ EE hB Q hbig hgeo
  refine ⟨fun p _ y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨y₀, Fs, hn, hF⟩ := GlobalTheory.T.exists_factor_classicalPoint_of_large_test o Ω S ρ M U₀ EE hB Q p y hy
    obtain ⟨t, ht⟩ := hgeo p y₀ hn Fs
    obtain ⟨c⟩ := hF t.u ht
    exact ⟨y₀, t, c, GlobalTheory.T.nonempty_testModel_to_closure hL o Ω S ρ M U₀ EE hB Q p y y₀ t c hbig⟩
  · haveI := hA.ft
    haveI := hA.char
    exact ((GlobalTheory.ZH.classical_points_and_local_regularity o Ω M U₀ hB.ov.normal).1 U₀ le_rfl hB.ov.ne z hz).1
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ExpCmp
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans GlobalTheory.UnitSec

def unitMap {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left) :
    (𝟙_ (Over S') ⊗ G').left ⟶ (𝟙_ (Over S) ⊗ G).left :=
  (snd (𝟙_ (Over S')) G').left ≫ F ≫ (λ_ G).inv.left

theorem unitMap_snd {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left) :
    unitMap F ≫ (snd (𝟙_ (Over S)) G).left = (snd (𝟙_ (Over S')) G').left ≫ F := by
  rw [unitMap, Category.assoc, Category.assoc, unit_inv_snd, Category.comp_id]

theorem eq_unitMap {S S' Z : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left)
    {r' : Z ⟶ (𝟙_ (Over S') ⊗ G').left} {r : Z ⟶ (𝟙_ (Over S) ⊗ G).left}
    (h : r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F) : r = r' ≫ unitMap F := by
  rw [unitMap, ← Category.assoc _ F, ← Category.assoc r', ← h, Category.assoc, snd_unit_inv, Category.comp_id]

theorem fst_unit {S : Scheme.{0}} (G : Over S) :
    (fst (𝟙_ (Over S)) G).left = (snd (𝟙_ (Over S)) G).left ≫ G.hom :=
  ((Category.comp_id _).symm.trans (Over.w (fst (𝟙_ (Over S)) G))).trans (Over.w (snd (𝟙_ (Over S)) G)).symm

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

theorem famφB_comp {φ : R →+* V} {D : DegPre R} {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left}
    (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {α' : D'.X} {α : D.X}
    (hc : (D'.c α').left ≫ β = spMap φ ≫ (D.c α).left) (i : Fin 4) :
    D'.famφB α' i ≫ β = β ≫ D.famφB α i := by
  have push : pushHom pb D'.P.A (cP D' _ α') = cP D _ α := Over.OverMorphism.ext (by
    show (D'.P.A.hom ≫ (D'.c α').left) ≫ β = (D'.P.A.hom ≫ spMap φ) ≫ (D.c α).left
    rw [Category.assoc, hc, Category.assoc])
  let ρ := pushHom pb D'.P.A (𝟙 _)
  have hρ : ρ.left = β := Category.id_comp _
  fin_cases i
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have e₁ : pushHom pb _ (𝟙 _ * cP D' _ α') = ρ ≫ (𝟙 _ * cP D _ α) := by
      rw [map_mul, push, MonObj.comp_mul, comp_cP, Category.comp_id]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom pb _ (cP D' _ α') = ρ ≫ cP D _ α := by rw [push, comp_cP]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom pb D'.P.A 1 = ρ ≫ (1 : D.P.A ⟶ D.P.A) := by rw [map_one, MonObj.comp_one]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)

theorem prod_fam {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (k : ℕ)
    {M : Type} [CommGroup M] (ω : (T.left ⟶ D.P.A.left) → M) (α : D.X) :
    (∏ a, ω (p.left ≫ D.famφB α a) ^ DegPre.famε k a) * ∏ a, ω (D.Oφ p α a) ^ Oinvε a =
      ω p.left ^ k := by
  have a₀ : p.left ≫ D.famφB α 0 = p.left := Category.comp_id _
  have a₁ : p.left ≫ D.famφB α 1 = D.Oφ p α 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul p (𝟙 _) (cP D _ α)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ α)))
  have a₂ : p.left ≫ D.famφB α 2 = D.Oφ p α 1 :=
    congrArg (fun z => z.left) (comp_cP D p α)
  have a₃ : p.left ≫ D.famφB α 3 = D.Oφ p α 3 :=
    congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) p)
  have a₄ : D.Oφ p α 2 = p.left := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

omit [IsDomain R] [IsDomain V] in
theorem exists_level {I : Ideal R} {I' : Ideal V} {φ : R →+* V} (hI : I.map φ ≤ I')
    {G : Over (Spec (CommRingCat.of R))} {G' : Over (Spec (CommRingCat.of V))} {F : G'.left ⟶ G.left}
    (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (e : ℕ) :
    ∃ m : (thickObj V I' e G').left ⟶ (thickObj R I e G).left,
      m ≫ (fstG I e G).left = (fstG I' e G').left ≫ F := by
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ :=
    Ideal.map_le_iff_le_comap.1 (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hI _)
  refine ⟨pullback.lift ((fstG I' e G').left ≫ F)
    (pullback.snd G'.hom (thick V I' e) ≫ spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle)) ?_, pullback.lift_fst _ _ _⟩
  have e2 : (fstG I' e G').left ≫ G'.hom = pullback.snd G'.hom (thick _ I' e) ≫ thick _ I' e := pullback.condition
  rw [Category.assoc, hF, ← Category.assoc, e2, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl



theorem expT_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → ∃ (σ' : U'.SecGT (𝟙_ _) k) (f' : ∀ α, SecBT D' (𝟙_ _) k α), U'.ExpT (𝟙_ _) k σ' f' ∧ (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') ∧ ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, gw C.v (r' ≫ famφT D' (𝟙_ _) α i) z (J (r' ≫ famφT D' (𝟙_ _) α i ≫ C.β)) (J' (r' ≫ famφT D' (𝟙_ _) α i)) ^ DegPre.famε k i).val * sval (f' α) r' z J' := by
  intro R V _ _ _ _ I I' φ hI D D' A A' G _ _ G' _ _ U U' F C k σ f hE
  classical
  have hcG : ∀ _ : Fin 1, (snd (𝟙_ _) G').left ≫ F = unitMap F ≫ (snd (𝟙_ _) G).left :=
    fun _ => (unitMap_snd F).symm
  have hcB : ∀ α i, famφT D' (𝟙_ _) α i ≫ C.β = unitMap C.β ≫ famφT D (𝟙_ _) (C.xe α) i := fun α i => by
    rw [famφT_eq, famφT_eq, ← Category.assoc (unitMap _), unitMap_snd, Category.assoc, Category.assoc,
      famφB_comp C.pbB (C.c_pr α)]
  obtain ⟨σ', hσ, -⟩ := SecPull.existsUnique_secPull _ _ _ _ U.P.L.L U'.P.L.L F U.P.L.isLB U'.P.L.isLB C.wL
    C.wL_map.gen (Fin 1) (fun _ => (snd (𝟙_ _) G').left) (fun _ => (snd (𝟙_ _) G).left) (fun _ => (k : ℤ))
    (unitMap F) hcG σ
  choose f' hf using fun α => (SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L C.β D.P.isLB D'.P.isLB C.v
    C.v_gen (Fin 4) (famφT D' (𝟙_ _) α) (famφT D (𝟙_ _) (C.xe α)) (DegPre.famε k)
    (unitMap C.β) (hcB α) (f (C.xe α))).exists
  have Hσ : ∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J' := by
    intro Z r' r hr z J J' hJ hJ'
    have := sec_val C.wL _ _ _ (unitMap F) hcG σ σ' r' z (hσ Z r' z) hJ hJ'
    rw [← eq_unitMap F hr, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, om, Category.assoc, ← hr] at this
    exact this
  have Hf : ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, om C.v z J J' (r' ≫ famφT D' (𝟙_ _) α i) ^ DegPre.famε k i).val * sval (f' α) r' z J' := by
    intro α Z r' r hr z J J' hJ hJ'
    have := sec_val C.v _ _ _ (unitMap C.β) (hcB α) (f (C.xe α)) (f' α) r' z (hf α Z r' z) hJ hJ'
    rw [← eq_unitMap C.β hr] at this
    exact this
  refine ⟨σ', f', fun e => ?_, Hσ, fun α Z r' r hr z J J' hJ hJ' => ?_⟩
  swap
  · have := Hf α Z r' r hr z J J' hJ hJ'
    simp only [om, Category.assoc] at this
    exact this
  obtain ⟨S, hS⟩ := hE e
  obtain ⟨m, hm⟩ := exists_level hI C.pb.1.w e
  refine ⟨S.map C.xe.symm.toEquiv.toEmbedding, fun Z x' rG' rB' hG' hB' _ z JG' J' hJG' hJ' => ?_⟩
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose JG hJG using fun ψ : Z ⟶ G.left => exists_chart U.P.L.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  have hJG : Good U.P.L.L z JG := hJG
  obtain ⟨x, hx⟩ : ∃ x : Z ⟶ (thickObj R I e G).left, x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F :=
    ⟨x' ≫ m, by rw [Category.assoc, hm]⟩
  obtain ⟨hq, hlev⟩ := C.lev e Z x' x hx
  obtain ⟨hT, hW⟩ := hlev z J J' hJ hJ'
  have hW := hW (JG (x ≫ (fstG I e G).left)) (JG' (x' ≫ (fstG I' e G').left)) (hJG _) (hJG' _)
  have rG₁ : (rG' ≫ unitMap F) ≫ (snd _ G).left = rG' ≫ (snd _ G').left ≫ F := by
    rw [Category.assoc, unitMap_snd]
  have rB₁ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = rB' ≫ (snd _ D'.P.A).left ≫ C.β := by
    rw [Category.assoc, unitMap_snd]
  have rG₂ : (rG' ≫ unitMap F) ≫ (snd _ G).left = x ≫ (fstG I e G).left := by
    rw [rG₁, hx, ← Category.assoc, hG', Category.assoc]
  have rB₂ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left := by
    rw [rB₁, ← hq, ← Category.assoc, hB', Category.assoc]
  have rBG : (rB' ≫ unitMap C.β) ≫ (fst _ D.P.A).left = (rG' ≫ unitMap F) ≫ (fst _ G).left := by
    rw [fst_unit, fst_unit, ← Category.assoc, ← Category.assoc, rG₂, rB₂, Category.assoc, Category.assoc]
    exact congrArg (x ≫ ·) ((Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm)
  obtain ⟨h0, hsum⟩ := hS Z x _ _ rG₂ rB₂ rBG z JG J hJG hJ
  have hF := fun α => Hf α Z rB' _ rB₁ z J J' hJ hJ'
  have Sg := Hσ Z rG' _ rG₁ z JG JG' hJG hJG'
  rw [rG₂, hG'] at Sg
  have hω : ∀ α, (∏ i : Fin 4, om C.v z J J' (rB' ≫ famφT D' (𝟙_ _) α i) ^ DegPre.famε k i) *
      ∏ i : Fin 4, gw C.v (x' ≫ D'.Oφ (U'.gt e).pG α i) z (J (x' ≫ D'.Oφ (U'.gt e).pG α i ≫ C.β))
          (J' (x' ≫ D'.Oφ (U'.gt e).pG α i)) ^ Oinvε i =
      gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) ^ k := by
    intro α
    have := prod_fam (U'.gt e).pG k (fun ψ => om C.v z J J' (x' ≫ ψ)) α
    have e₁ : ∀ i, rB' ≫ famφT D' (𝟙_ _) α i = x' ≫ (U'.gt e).pG.left ≫ D'.famφB α i := fun i => by
      rw [famφT_eq, ← Category.assoc, hB', Category.assoc]
    rw [← hq, ← Category.assoc x' _ C.β]
    refine Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_)
      (Finset.prod_congr rfl fun i _ => ?_)) this
    · rw [e₁]
    · rw [← Category.assoc x' _ C.β]; rfl
  refine ⟨fun α' hα => ?_, ?_⟩
  · have hi : C.xe α' ∉ S := fun hc => hα (Finset.mem_map.2 ⟨C.xe α', hc, C.xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').symm.trans (h0 _ hi))
  · refine (gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, hW, mul_pow, Units.val_mul,
      _root_.mul_assoc, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← Sg, hsum, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨α', rfl⟩ := C.xe.surjective y
    have e₀ : C.xe.symm.toEquiv.toEmbedding (C.xe α') = α' := C.xe.symm_apply_apply α'
    rw [e₀, hF α', hT α', ← hω α', Units.val_mul, Units.val_mul]
    ring

end GlobalTheory.ExpCmp
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Relabel

def TwJ {O : Type} [CommRing O] {N N' : NumD O} {k : ℕ} (β : N.Form k) (u r : Oˣ) (J : NumD.Iso (N.twist β u) N')
    {j : ℕ} (q : N.QT j) (q' : N'.QT j) : Prop :=
  ∃ p : (N.twist β u).QT j, TwRel β u r q p ∧ q'.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q'.1.2
section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} {O : Type} [CommRing O] [StarRing O]

def actV (ν : NumOf D F N) (oa : D.P.OAct O) (x : O) (b : N.A) : N.A := ν.eA.symm (ν.eA b ≫ oa.act x)

def RosV (ν : NumOf D F N) (oa : D.P.OAct O) (x : O) (ρ : N.A → N.A → F) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.act (star x)) (oa.act x)) rosatiε), u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) ∧
    ∀ b b', ρ b b' = vF u (lift (ν.eA b) (ν.eA b')).left ν.J

def ActCompat [Module O D.X] (ν : NumOf D F N) (oa : D.OAct O) {R' : Type} [CommRing R'] [IsDomain R'] {D' : DegPre R'}
    [Algebra (FractionRing R') F] {N' : NumD F} [Module O D'.X] (ν' : NumOf D' F N') (oa' : D'.OAct O) {k : ℕ}
    (β : N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (N.twist β u) N') : Prop :=
  ∀ j, 0 < j → ∀ (x : O) (p₀ p₁ : QkPt D F j) (p₀' p₁' : QkPt D' F j) q₀ q₁ q₀' q₁', QkAct oa x p₀ p₁ → ν.QPt p₀ q₀ →
    ν.QPt p₁ q₁ → TwJ β u (r j) J q₀ q₀' → TwJ β u (r j) J q₁ q₁' → ν'.QPt p₀' q₀' → ν'.QPt p₁' q₁' →
    QkAct oa' x p₀' p₁'
end
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {K : Type} [Field K]

abbrev FullI (o : Full D K) : Type :=
  letI := H.starRing
  TateIso D K (baseOver (Sp K) ⟶ o.P.A) (fun a g => g ≫ o.oa.act a) (fun n g g' c => WeilIs o.P.A o.P.L n g g' (unitOn c))

def withI (o : Full D K) (I : FullI o) : Full D K := { o with I := I }

end GlobalTheory.Relabel
end
end
