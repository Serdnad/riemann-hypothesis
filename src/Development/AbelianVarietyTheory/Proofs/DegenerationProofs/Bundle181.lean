module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle178
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle168
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.AbelianPart

theorem isProper_snd_iff {Z A B T : Scheme.{0}} (e : A ≅ B) (f : A ⟶ Z) (g : B ⟶ Z) (h : e.hom ≫ g = f)
    (t : T ⟶ Z) : IsProper (pullback.snd f t) ↔ IsProper (pullback.snd g t) := by
  subst h
  have P : IsPullback (pullback.fst g t ≫ e.inv) (pullback.snd g t) (e.hom ≫ g) t :=
    IsPullback.of_iso (IsPullback.of_hasPullback g t) (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  constructor
  · intro h
    rw [← P.isoPullback_hom_snd]
    infer_instance
  · intro h
    rw [← P.isoPullback_inv_snd]
    infer_instance

theorem abLocus_congr {Z : Scheme.{0}} (A B : Over Z) (e : A.left ≅ B.left) (h : e.hom ≫ B.hom = A.hom) :
    abLocus A = abLocus B := by
  ext z
  exact ⟨fun H K _ _ t ht => (isProper_snd_iff e _ _ h t).1 (H K t ht),
    fun H K _ _ t ht => (isProper_snd_iff e _ _ h t).2 (H K t ht)⟩

theorem isProper_snd_of_le {Z A : Scheme.{0}} (f : A ⟶ Z) {U V : Z.Opens} (h : U ≤ V)
    [IsProper (pullback.snd f V.ι)] : IsProper (pullback.snd f U.ι) := by
  have P := (IsPullback.of_hasPullback (pullback.snd f V.ι) (Z.homOfLE h)).paste_horiz
    (IsPullback.of_hasPullback f V.ι)
  rw [Scheme.homOfLE_ι] at P
  rw [← P.isoPullback_inv_snd]
  infer_instance

theorem not_mem_abLocus (C : GlobalTheory.ZJ.Core) (L : C.Law) {p : ℕ} [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ C.Z)
    (τ : C.Test y) (h : ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j))) :
    y (GlobalTheory.ZJ.cPt p) ∉ abLocus C.GG := by
  intro hm
  obtain ⟨hsep, hlft, -⟩ := GlobalTheory.ZJ.core_basic C
  have hc : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀ := (L.test p y τ).1
  have P := (IsPullback.of_hasPullback τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)).paste_horiz hc
  rw [Category.assoc, τ.fac] at P
  refine h ((GlobalTheory.ZJ.AbelianLocus.mem_abLocus_iff C.GG P (IsLocalRing.closedPoint (GlobalTheory.ZJ.kb p))).1 ?_)
  have e : GlobalTheory.ZJ.rPt p (IsLocalRing.closedPoint (GlobalTheory.ZJ.kb p)) = GlobalTheory.ZJ.cPt p :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue (GlobalTheory.ZJ.OO p))
  rw [← e] at hm
  exact hm

theorem ab : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀), (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) → Nonempty ex.core.Law → ex.core.HasTests → ex.core.HasCharts → IsOpen {z : M.Z | S.TT M z = ⊥} → (∀ w : Q.P.left, IsClosed ({w} : Set Q.P.left) → S.TT M (Q.P.hom w) = ⊥ → w ∈ Q.G) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.TT M z ≠ ⊥ → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (τ : ex.core.Test y), y (GlobalTheory.ZJ.cPt p) = z ∧ ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j))) → Z.Ab := by
  rintro o Ω _ _ _ _ S ρ M U₀ EE Q ex Z ⟨e, he, -⟩ ⟨L⟩ hT hC hO h₁ h₂
  obtain ⟨hab, hpr⟩ := GlobalTheory.ZJ.AbelianLocus.abLocus_eq ex.core L hT hC ⟨_, hO⟩ h₁ (fun z hz hn => by
    obtain ⟨p, _, y, τ, rfl, h⟩ := h₂ z hz hn
    exact not_mem_abLocus ex.core L y τ h)
  have hE : abLocus Z.G = {z | S.TT M z = ⊥} := (abLocus_congr Z.G ex.core.GG e he).trans hab
  refine ⟨hE, fun W hW => ?_⟩
  rw [hE] at hW
  exact (isProper_snd_iff e _ _ he W.ι).2
    (@isProper_snd_of_le _ _ ex.core.GG.hom W ⟨_, hO⟩ hW hpr)

end GlobalTheory.ZH.AbelianPart
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.LatChar

theorem eq_zero_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  have hne' : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (X.basicOpen f).isOpen.isLocallyClosed
  have hb : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ X.basicOpen f := fun q _ => by
    show pointOfClosedPoint π y hc q ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply π y hc q]
    exact hy
  have hU : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
  exact ((CrdCalc.isUnit_valR_iff _ U hU f).2 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem lin_eq_zero {k : Type} [Field k] [IsAlgClosed k] (Φ : FibPre k) [Smooth Φ.G.hom] {N : ℕ}
    {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X} {F : J → (Φ.H 1).Sec}
    (hG : Φ.Good N q cls F) (a : J → k) (h : ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, ∑ i, a i * v i = 0) : a = 0 := by
  have : IsReduced Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced Φ.G.hom
  refine GlobalTheory.ZH.WtLin.linIndep k Φ N q J cls F hG a fun l => ?_
  refine eq_zero_of_points Φ.G.hom _ _ fun x hx hU => ?_
  have h1 := h _ ⟨x, hx, l, 1, hU, fun _ => rfl⟩

  rw [CrdCalc.valR_eq x _ hU, map_sum, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, Units.val_one, _root_.one_mul]
  exact congrArg (· * _) (GlobalTheory.Points.valR_constFn_of_section Φ.G.hom x hx _ hU (a i))

theorem mem_span_iff {p : ℕ} [Fact p.Prime] {J A : Type} [Fintype J] [Nonempty J] (B : Matrix J J (PadicAlgCl p))
    (hB : B.det ≠ 0) (T : Set A) (v : A → J → PadicAlgCl p) (κ : ℝ) (hκ : 0 < κ)
    (hle : ∀ a ∈ T, ∀ i, ‖B.mulVec (v a) i‖ ≤ κ)
    (hdet : ∀ c : J → OO p, (∀ a ∈ T, ‖∑ i, (c i : PadicAlgCl p) * B.mulVec (v a) i‖ < κ) →
      ∀ i, ‖(c i : PadicAlgCl p)‖ < 1) (e : J → PadicAlgCl p) :
    e ∈ Submodule.span (OO p) (Set.range B) ↔ ∀ a ∈ T, ‖e ⬝ᵥ v a‖ ≤ κ := by
  have key : ∀ (c : J → PadicAlgCl p) (w : J → PadicAlgCl p),
      (B.vecMul c) ⬝ᵥ w = ∑ i, c i * B.mulVec w i := fun c w => (Matrix.dotProduct_mulVec c B w).symm
  have hvec : ∀ c : J → OO p, ∑ i, c i • B i = B.vecMul fun i => (c i : PadicAlgCl p) := fun c => by
    ext j
    rw [Finset.sum_apply]
    rfl
  refine (Submodule.mem_span_range_iff_exists_fun (v := fun i => B i) _).trans ?_
  constructor
  · rintro ⟨c, rfl⟩ a ha
    rw [hvec, key]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hκ.le fun i _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((mem_OO_iff _).1 (c i).2)).trans (hle a ha i)
  · intro h
    obtain ⟨c, rfl⟩ : ∃ c, B.vecMul c = e := ⟨B⁻¹.vecMul e, by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB), Matrix.vecMul_one]⟩
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ‖c i‖
    by_cases h1 : ‖c i₀‖ ≤ 1
    · exact ⟨fun i => ⟨c i, (mem_OO_iff _).2 ((hi₀ i).trans h1)⟩, hvec _⟩
    exfalso
    rw [not_le] at h1
    have h0 : 0 < ‖c i₀‖ := one_pos.trans h1
    have h0' : c i₀ ≠ 0 := norm_pos_iff.1 h0
    have := hdet (fun i => ⟨c i / c i₀, (mem_OO_iff _).2 (by
      rw [norm_div]; exact (div_le_one h0).2 (hi₀ i))⟩) (fun a ha => by
        have h2 := h a ha
        rw [key] at h2
        have e : ∑ i, c i / c i₀ * B.mulVec (v a) i = (∑ i, c i * B.mulVec (v a) i) / c i₀ := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
        show ‖∑ i, c i / c i₀ * B.mulVec (v a) i‖ < κ
        rw [e, norm_div, div_lt_iff₀ h0]
        exact h2.trans_lt (lt_mul_of_one_lt_right hκ h1)) i₀
    simp [div_self h0'] at this

theorem mem_lattice_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)) (κ : ℝ), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → u.Link σ b → b.det ≠ 0 → 0 < κ → (∀ a ∈ l.yy.ker, IsGreatest (Set.range fun i => ‖(b.map (algebraMap _ (PadicAlgCl p))).mulVec (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i‖) κ) → ∀ e : S.J → PadicAlgCl p, e ∈ Submodule.span (OO p) (Set.range (b.map (algebraMap _ (PadicAlgCl p)))) ↔ ∀ a ∈ l.yy.ker, ‖e ⬝ᵥ (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩)‖ ≤ κ := by
  intro L o Ω _ _ _ _ S ρ p _ y₀ u l σ cls md b κ hBig hy hL hb hκ hmax e
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hB : Big S.g S.N (S.r * S.N) := ⟨(GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre L o Ω S ρ p y₀ u).2.2.2.1, hBig.1, hBig.2.1⟩
  obtain ⟨hN, htor, -⟩ := GlobalTheory.T.specialFibre_torsion_eq_reductions L o Ω S ρ p y₀ u l σ cls md hy
  have pb : IsPullback md.r md.Φ.G.hom u.G.hom (rPt p ≫ spMap u.j) := md.cart.1
  have hs : Smooth u.G.hom := md.smooth.smooth
  have : Smooth md.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  refine mem_span_iff _ ?_ (l.yy.ker : Set S.Gam) (fun a i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) κ hκ
    (fun a ha i => (hmax a ha).2 ⟨i, rfl⟩) (fun c hc => ?_) e
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hb
  have hev : ∀ v : S.J → kb p, MvPolynomial.eval v (∑ i, MvPolynomial.C (IsLocalRing.residue (OO p) (c i)) *
      MvPolynomial.X i) = ∑ i, IsLocalRing.residue (OO p) (c i) * v i := fun v => by simp
  have hz := GlobalTheory.T.form_vanishes_of_torsion_torusExtension L.1 L.2.1 (kb p) md.Φ S.g S.N (S.r * S.N) _ S.J _ md.F md.pol hB md.good md.dim hN 1
    (∑ i, MvPolynomial.C (IsLocalRing.residue (OO p) (c i)) * MvPolynomial.X i)
    (Nat.mul_pos (pow_pos (by have := hB.four; omega) _) (Nat.factorial_pos _))
    (MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X _ i).C_mul _) ?_
  · have h0 := lin_eq_zero md.Φ md.good (fun i => IsLocalRing.residue (OO p) (c i)) fun v hv =>
      (hev v).symm.trans (hz v hv)
    intro i
    exact (not_isUnit_OO_iff _).1 fun hu => (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu (congrFun h0 i)
  intro x hx
  obtain ⟨a, ha, z, a', hz, hg, hA, hr⟩ := htor x hx
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists md.isLB σ z
  obtain ⟨⟨i₀, -, hi₀⟩, x', hx', hc'⟩ := GlobalTheory.T.exists_unit_weightZero_integral_coords L.1 L.2.1 p u.V u.j u.G S.g S.N (S.r * S.N) _ l.q _ S.J σ cls
    md hB z w hz hw
  have hxx : x'.left = x.left := pb.hom_ext (hx'.trans hr) ((Over.w x').trans (Over.w x).symm)
  refine ⟨_, hxx ▸ hc', ?_⟩
  have h1 := hL a' _ (hA ▸ (GlobalTheory.T.torsionValues_coords_operator_permute L o Ω S ρ).1 _ y₀ a)
  have h2 := CrdCalc.crd_map (OO p).subtype hw
  rw [show spMap (OO p).subtype ≫ z = u.toG a' from hg] at h2
  obtain ⟨t, ht⟩ := CrdCalc.crd_unique h2 h1
  have hn : κ ≤ ‖(t : PadicAlgCl p)‖ := by
    obtain ⟨i, hi⟩ := (hmax a ha).1
    rw [← hi]
    beta_reduce
    rw [ht i, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 (w i).2)
  have h3 := hc a ha
  have e3 : ∑ i, (c i : PadicAlgCl p) * (b.map (algebraMap _ (PadicAlgCl p))).mulVec
      (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i = t * ((∑ i, c i * w i : OO p) : PadicAlgCl p) := by

    rw [show ((∑ i, c i * w i : OO p) : PadicAlgCl p) = (OO p).subtype (∑ i, c i * w i) from rfl, map_sum,
    Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht i, map_mul, mul_left_comm]
    rfl
  rw [e3, norm_mul] at h3
  have h4 : ‖((∑ i, c i * w i : OO p) : PadicAlgCl p)‖ < 1 := by
    by_contra h5
    exact absurd h3 (not_lt.2 (hn.trans (le_mul_of_one_le_right (norm_nonneg _) (not_lt.1 h5))))
  rw [hev]
  have h5 : IsLocalRing.residue (OO p) (∑ i, c i * w i) = 0 := by
    by_contra h6
    exact (not_isUnit_OO_iff _).2 h4 ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h6)
  simpa using h5

end GlobalTheory.ZH.LatChar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem mem_span_rows_iff_vecMul_inv {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {c : Matrix J J Ω} (hc : c.det ≠ 0) (v : J → Ω) :
    v ∈ Submodule.span S (Set.range c) ↔ ∀ j, Matrix.vecMul v c⁻¹ j ∈ S := by
  have hu : IsUnit c.det := isUnit_iff_ne_zero.2 hc
  have key : ∀ a : J → S, ∑ i, a i • c i = Matrix.vecMul (fun i => (a i : Ω)) c := fun a => by
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  refine (Submodule.mem_span_range_iff_exists_fun S (v := fun i => c i)).trans ?_
  constructor
  · rintro ⟨a, rfl⟩ j
    rw [key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
    exact (a j).2
  · intro h
    refine ⟨fun j => ⟨_, h j⟩, ?_⟩
    rw [key]
    show Matrix.vecMul (Matrix.vecMul v c⁻¹) c = v
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o]
  {J : Type} [Fintype J] [DecidableEq J]

theorem mem_span_rows_of_forall_valuationRing (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {c : Matrix J J Ω} (hc : c.det ≠ 0) (x : M.Z) (v : J → Ω)
    (h : ∀ ξ : M.Z, ξ ⤳ x → ValuationRing (M.O ξ) → v ∈ Submodule.span (M.O ξ) (Set.range c)) :
    v ∈ Submodule.span (M.O x) (Set.range c) :=
  (mem_span_rows_iff_vecMul_inv _ hc v).2 fun j => M.mem_O_of_forall_valuationRing hn x _ fun ξ hξ hv =>
    (mem_span_rows_iff_vecMul_inv _ hc v).1 (h ξ hξ hv) j

theorem span_rows_eq_of_forall_valuationRing (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {b c : Matrix J J Ω} (hb : b.det ≠ 0) (hc : c.det ≠ 0) (x : M.Z)
    (h : ∀ ξ : M.Z, ξ ⤳ x → ValuationRing (M.O ξ) →
      Submodule.span (M.O ξ) (Set.range b) = Submodule.span (M.O ξ) (Set.range c)) :
    Submodule.span (M.O x) (Set.range b) = Submodule.span (M.O x) (Set.range c) :=
  le_antisymm
    (Submodule.span_le.2 fun v hv => M.mem_span_rows_of_forall_valuationRing hn hc x v fun ξ hξ hr =>
      (h ξ hξ hr).le (Submodule.subset_span hv))
    (Submodule.span_le.2 fun v hv => M.mem_span_rows_of_forall_valuationRing hn hb x v fun ξ hξ hr =>
      (h ξ hξ hr).ge (Submodule.subset_span hv))

end RatModel

theorem exists_lat_of_height_le_one :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o]
      [JacobsonSpace M.Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (J : Type) [Fintype J] [DecidableEq J]
      (b : M.Z → Matrix J J Ω) (D : ∀ ξ : M.Z, Submodule (M.O ξ) (J → Ω)), (∀ z, (b z).det ≠ 0) →
      (∀ z, IsClosed ({z} : Set M.Z) → ∃ W : M.Z.Opens, z ∈ W ∧ ∀ ξ ∈ W, ValuationRing (M.O ξ) →
        Submodule.span (M.O ξ) (Set.range (b z)) = D ξ) →
      ∃ EE : M.Lat J, (∀ z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) (Set.range (b z))) ∧
        ∀ (W : M.Z.Opens) (c : Matrix J J Ω), c.det ≠ 0 →
          (∀ ξ ∈ W, ValuationRing (M.O ξ) → D ξ = Submodule.span (M.O ξ) (Set.range c)) →
          ∀ x ∈ W, EE.E x = Submodule.span (M.O x) (Set.range c) := by
  intro o Ω _ _ _ M _ _ hn J _ _ b D hb h
  have hx : ∀ x : M.Z, ∃ (z : M.Z) (W : M.Z.Opens), x ∈ W ∧ ∀ ξ ∈ W, ValuationRing (M.O ξ) →
      Submodule.span (M.O ξ) (Set.range (b z)) = D ξ := fun x => by
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set M.Z))
      ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    obtain ⟨W, hzW, hW⟩ := h z hzc
    exact ⟨z, W, (specializes_iff_mem_closure.2 hz).mem_open W.isOpen hzW, hW⟩
  choose g U hU hg using hx
  have main : ∀ (W : M.Z.Opens) (c : Matrix J J Ω), c.det ≠ 0 →
      (∀ ξ ∈ W, ValuationRing (M.O ξ) → D ξ = Submodule.span (M.O ξ) (Set.range c)) →
      ∀ x ∈ W, Submodule.span (M.O x) (Set.range (b (g x))) = Submodule.span (M.O x) (Set.range c) :=
    fun W c hc hW x hx => M.span_rows_eq_of_forall_valuationRing hn (hb _) hc x fun ξ hξ hr =>
      (hg x ξ (hξ.mem_open (U x).isOpen (hU x)) hr).trans (hW ξ (hξ.mem_open W.isOpen hx) hr)
  refine ⟨⟨fun x => Submodule.span (M.O x) (Set.range (b (g x))), fun x => ⟨U x, b (g x), hU x, hb _,
    main _ _ (hb _) fun ξ hξ hr => (hg x ξ hξ hr).symm⟩⟩, fun z hz => ?_, main⟩
  obtain ⟨W, hzW, hW⟩ := h z hz
  exact main W _ (hb z) (fun ξ hξ hr => (hW ξ hξ hr).symm) z hzW

end GlobalTheory.ZH
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.arcData_descends_from_completeDVR : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ : Sp R ⟶ Y.X) (y : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → ∀ (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t), P.TorsionIso → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ g : R →+* V, Function.Injective g → I.map g ≤ IsLocalRing.maximalIdeal V → ¬ IsUnit (g u) → (∀ x, x ≠ 0 → IsUnit (g (f x))) → Y.HasArcData a (IsLocalRing.maximalIdeal V) (g.comp f) (g u) (spMap g ≫ χ) → Y.HasArcData a I f u χ := by
  first | exact @GlobalTheory.ArcDataDescent.hasArcData_descends | exact GlobalTheory.ArcDataDescent.hasArcData_descends | (intros; apply GlobalTheory.ArcDataDescent.hasArcData_descends <;> assumption)
end
