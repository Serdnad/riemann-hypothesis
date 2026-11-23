module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.GeoModel
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.UT
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
variable {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  refine ⟨?_⟩
  have h : Function.Injective (OO p).subtype := Subtype.val_injective
  have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 h]; exact bot_le)
  exact this

theorem exists_intGood (u : ρ.UTest p y₀) :
    ∃ J, u.IntGood J ∧ ∀ z, Good u.D.toPre.P.L z J := by
  classical
  have hsep : IsSeparated u.D.toPre.P.A.hom := by
    have := u.D.toPre.P.isAb.proper
    infer_instance
  have hc : ∀ x : u.D.toPre.P.A.left, ∃ i, x ∈ u.D.toPre.P.L.U i := fun x =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [u.D.toPre.P.isLB.cover]; trivial)
  choose ch hch using hc
  have := isDominant_gPt p
  let P : (Sp (PadicAlgCl p) ⟶ u.D.toPre.P.A.left) → Prop := fun φ =>
    ∃ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, ψ ≫ u.D.toPre.P.A.hom = spMap u.j ∧ gPt p ≫ ψ = φ
  let J : (Sp (PadicAlgCl p) ⟶ u.D.toPre.P.A.left) → u.D.toPre.P.L.ι := fun φ =>
    if h : P φ then ch (h.choose (cPt p)) else ch (φ (IsLocalRing.closedPoint _))
  have key : ∀ (ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left) (w : Sp (OO p)), ψ w ∈ u.D.toPre.P.L.U (ch (ψ (cPt p))) :=
    fun ψ w => ((IsLocalRing.specializes_closedPoint w).map ψ.continuous).mem_open
      (u.D.toPre.P.L.U _).isOpen (hch _)
  refine ⟨J, fun ψ hψ => ?_, fun z φ => ?_⟩
  · have h : P (gPt p ≫ ψ) := ⟨ψ, hψ, rfl⟩
    have e : h.choose = ψ :=
      ext_of_isDominant_of_isSeparated u.D.toPre.P.A.hom (h.choose_spec.1.trans hψ.symm) (gPt p) h.choose_spec.2
    have hJ : J (gPt p ≫ ψ) = ch (ψ (cPt p)) := by
      simp only [J]; rw [dite_eq_left h, e]
    intro w _
    show ψ w ∈ u.D.toPre.P.L.U (J (gPt p ≫ ψ))
    rw [hJ]; exact key ψ w
  · show φ z ∈ u.D.toPre.P.L.U (J φ)
    by_cases h : P φ
    · have hJ : J φ = ch (h.choose (cPt p)) := by simp only [J]; rw [dite_eq_left h]
      rw [hJ]
      have e : φ z = h.choose (gPt p z) := by
        conv_lhs => rw [← h.choose_spec.2]
        rfl
      rw [e]; exact key _ _
    · have hJ : J φ = ch (φ (IsLocalRing.closedPoint _)) := by simp only [J]; rw [dite_eq_right h]
      rw [hJ]
      have e : z = IsLocalRing.closedPoint (PadicAlgCl p) := Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _
      rw [e]; exact hch _

theorem gtN_unique (u : ρ.UTest p y₀) (g : GtPtF u.D.toPre (PadicAlgCl p)) (ν ν' : u.D.toPre.X → ℝ)
    (h : u.GtN g ν) (h' : u.GtN g ν') : ν = ν' := by
  obtain ⟨J, hJ, -⟩ := exists_intGood u
  funext χ
  have := (h J hJ χ).symm.trans (h' J hJ χ)
  simpa using this

theorem j_mem_max (u : ρ.UTest p y₀) (x : u.V) (hx : x ∈ IsLocalRing.maximalIdeal u.V) :
    u.j x ∈ IsLocalRing.maximalIdeal (OO p) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have h1 : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ x) * (y : PadicAlgCl p) = 1 :=
    congrArg Subtype.val hy
  have h2 : (y : PadicAlgCl p) = algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ x)⁻¹ := by
    rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right h1
  obtain ⟨z, hz⟩ := (u.norm_le (algebraMap u.V _ x)⁻¹).1 (h2 ▸ (mem_OO_iff _).1 y.2)
  have h0 : algebraMap u.V (FractionRing u.V) x ≠ 0 := fun h => by simp [h] at h1
  refine IsUnit.of_mul_eq_one z (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]

theorem norm_unit {X : Scheme.{0}} (ψ : Sp (OO p) ⟶ X) (U : X.Opens) (h : ⊤ ≤ ψ ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    ‖Geo.Tor.valR (gPt p ≫ ψ) U f.val‖ = 1 := by
  rw [GlobalTheory.Points.valR_spMap_comp _ ψ U h]
  have hu : IsUnit (Geo.Tor.valR ψ U f.val) := by
    rw [GlobalTheory.Points.valR_eq ψ U h]; exact f.isUnit.map _
  have h1 := (not_isUnit_OO_iff (Geo.Tor.valR ψ U f.val)).not.1 (not_not.2 hu)
  exact le_antisymm ((mem_OO_iff _).1 (Subtype.prop _)) (not_lt.1 h1)

theorem norm_indep {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Sp (OO p) ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L (fun k => gPt p ≫ ψ k) ε)) (ht : t.IsGen) (j j' : K → L.ι)
    (hj : ∀ k, ⊤ ≤ ψ k ⁻¹ᵁ L.U (j k)) (hj' : ∀ k, ⊤ ≤ ψ k ⁻¹ᵁ L.U (j' k)) :
    ‖valF (𝟙 (Sp (PadicAlgCl p))) _ (t.s j).val‖ = ‖valF (𝟙 (Sp (PadicAlgCl p))) _ (t.s j').val‖ ∧
      valF (𝟙 (Sp (PadicAlgCl p))) _ (t.s j).val ≠ 0 := by
  have a : ⊤ ≤ (𝟙 (Sp (PadicAlgCl p))) ⁻¹ᵁ LB.wchart L (fun k => gPt p ≫ ψ k) j :=
    fun w _ => Set.mem_iInter.2 fun k => hj k (x := gPt p w) trivial
  have a' : ⊤ ≤ (𝟙 (Sp (PadicAlgCl p))) ⁻¹ᵁ LB.wchart L (fun k => gPt p ≫ ψ k) j' :=
    fun w _ => Set.mem_iInter.2 fun k => hj' k (x := gPt p w) trivial
  have b : ⊤ ≤ (𝟙 (Sp (PadicAlgCl p))) ⁻¹ᵁ
      (LB.wchart L (fun k => gPt p ≫ ψ k) j ⊓ LB.wchart L (fun k => gPt p ≫ ψ k) j') :=
    fun w _ => ⟨a (x := w) trivial, a' (x := w) trivial⟩
  refine ⟨?_, ?_⟩
  · let E := Units.map (GlobalTheory.Points.valMap (𝟙 (Sp (PadicAlgCl p))) _ b).hom.toMonoidHom
    let Nn : (PadicAlgCl p)ˣ →* ℝˣ := Units.map (normHom (α := PadicAlgCl p)).toMonoidHom
    have e := congrArg (fun x => Nn (E x)) (ht j j')
    have hg : Nn (E ((LB.LinComb L (fun k => gPt p ≫ ψ k) ε).g j j')) = 1 := by
      show Nn (E (∏ k, _)) = 1
      rw [map_prod, map_prod]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [map_zpow, map_zpow]
      have : Nn (E (res (le_inf (inf_le_left.trans (LB.wchart_le L (fun k => gPt p ≫ ψ k) j k))
          (inf_le_right.trans (LB.wchart_le L (fun k => gPt p ≫ ψ k) j' k)) :
          LB.wchart L (fun k => gPt p ≫ ψ k) j ⊓ LB.wchart L (fun k => gPt p ≫ ψ k) j' ≤
            (gPt p ≫ ψ k) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
          (pullU (gPt p ≫ ψ k) _ (L.g (j k) (j' k))))) = 1 := by
        apply Units.ext
        have h1 := norm_unit (ψ k) (L.U (j k) ⊓ L.U (j' k))
          (fun w _ => ⟨hj k (x := w) trivial, hj' k (x := w) trivial⟩) (L.g (j k) (j' k))
        rw [← Category.id_comp (gPt p ≫ ψ k), GlobalTheory.Points.valR_comp] at h1
        exact (congrArg norm ((GlobalTheory.Points.valR_eq _ _ b _).symm.trans
          (GlobalTheory.Points.valR_res (U := (gPt p ≫ ψ k) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k))) _
          (le_inf (inf_le_left.trans (LB.wchart_le L (fun k => gPt p ≫ ψ k) j k))
          (inf_le_right.trans (LB.wchart_le L (fun k => gPt p ≫ ψ k) j' k))) b _))).trans h1
      exact (congrArg (· ^ ε k) this).trans (one_zpow _)
    have e2 : Nn (E (res inf_le_left (t.s j))) = Nn (E (res inf_le_right (t.s j'))) := by
      refine e.trans ?_
      refine (congrArg Nn (map_mul E _ _)).trans ((map_mul Nn _ _).trans ?_)
      exact (congrArg (· * _) hg).trans (one_mul _)
    have e3 := congrArg Units.val e2
    refine (congrArg norm ((GlobalTheory.Points.valR_eq _ _ b _).symm.trans
      (GlobalTheory.Points.valR_res _ inf_le_left b (t.s j).val))).symm.trans (Eq.trans e3 ?_)
    exact congrArg norm ((GlobalTheory.Points.valR_eq _ _ b _).symm.trans
      (GlobalTheory.Points.valR_res _ inf_le_right b (t.s j').val))
  · exact (GlobalTheory.Points.valR_eq _ _ a (t.s j).val).trans_ne ((t.s j).isUnit.map _).ne_zero

theorem exists_ext (u : ρ.UTest p y₀) (b : TF (R := u.V) (PadicAlgCl p) ⟶ u.D.toPre.P.A) :
    ∃ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, ψ ≫ u.D.toPre.P.A.hom = spMap u.j ∧ gPt p ≫ ψ = b.left := by
  have hp := u.D.toPre.P.isAb.proper
  have hv : ValuativeCriterion.Existence u.D.toPre.P.A.hom := by
    have : UniversallyClosed u.D.toPre.P.A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at this
    exact this.1
  have w : b.left ≫ u.D.toPre.P.A.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (OO p) (PadicAlgCl p))) ≫ spMap u.j := by
    refine (Over.w b).trans ?_
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hv { R := OO p, K := PadicAlgCl p, i₁ := b.left, i₂ := spMap u.j, commSq := ⟨w⟩ }
  exact ⟨l.l, l.fac_right, l.fac_left⟩

theorem exists_gtN (u : ρ.UTest p y₀) (g : GtPtF u.D.toPre (PadicAlgCl p)) : ∃ ν, u.GtN g ν := by
  obtain ⟨J₀, hJ₀, -⟩ := exists_intGood u
  refine ⟨fun χ => -Real.log ‖valF (𝟙 (Sp (PadicAlgCl p))) _
    ((g.s χ).s (fun k => J₀ (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k))).val‖, fun J hJ χ => ?_⟩
  have h : ∀ k, ∃ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, ψ ≫ u.D.toPre.P.A.hom = spMap u.j ∧
      gPt p ≫ ψ = DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k := by
    intro k
    fin_cases k <;> exact exists_ext u _
  choose ψ h1 h2 using h
  have key : ∀ (φ : Fin 4 → (Sp (PadicAlgCl p) ⟶ u.D.toPre.P.A.left)) (_ : ∀ k, gPt p ≫ ψ k = φ k)
      (t : LB.Gen (LB.LinComb u.D.toPre.P.L φ DegPre.gtε)), t.IsGen →
      ‖valF (𝟙 (Sp (PadicAlgCl p))) _ (t.s (fun k => J (φ k))).val‖ =
        Real.exp (- -Real.log ‖valF (𝟙 (Sp (PadicAlgCl p))) _ (t.s (fun k => J₀ (φ k))).val‖) := by
    intro φ hφ t ht
    obtain rfl : φ = fun k => gPt p ≫ ψ k := funext fun k => (hφ k).symm
    have A := norm_indep _ ψ _ t ht _ _ (fun k => hJ₀ _ (h1 k)) (fun k => hJ _ (h1 k))
    rw [neg_neg, Real.exp_log (norm_pos_iff.2 A.2)]
    exact A.1.symm
  exact key _ h2 (g.s χ) (g.isGen χ)
end GlobalTheory.ZH.GeoModel
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

structure Clos (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) where
  u₀ : U₀.toScheme ⟶ Sp S.R
  u₀_pt : ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap S.R.val.toRingHom
  P : Over M.Z
  [intP : IsIntegral P.left]
  proper : IsProper P.hom
  proj : IsProjOver (P.hom ≫ M.s)
  a₀ : pullback ρ.P.A.hom u₀ ⟶ P.left
  cart : IsPullback a₀ (pullback.snd ρ.P.A.hom u₀) P.hom U₀.ι
  O1 : LB P.left
  isLB : O1.IsLB
  st : S.J → O1.Sec
  crd : ∀ (K : Type) [Field K] (x : Sp K ⟶ pullback ρ.P.A.hom u₀) (v : S.J → K),
    ρ.Crd (x ≫ pullback.fst _ _) v → Crd O1 st (x ≫ a₀) v
  Λ : Type
  W : Λ → M.Z.Opens
  aff : ∀ l, IsAffineOpen (W l)
  ne : ∀ l, (W l : Set M.Z).Nonempty
  cover : ⨆ l, W l = ⊤
  B : Λ → Matrix S.J S.J Ω
  basis : ∀ l, ∀ z ∈ W l, EE.E z = Submodule.span (M.O z) (Set.range (B l))
  c : ∀ l, Matrix S.J S.J Γ(M.Z, W l)
  c_inv : ∀ l, (c l).map (valF M.pt (W l)) * B l = 1
  σ : ∀ l, S.J → (O1.pull (P.hom ⁻¹ᵁ W l).ι).Sec
  rel : ∀ l (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ (P.hom ⁻¹ᵁ W l).toScheme) (w : S.J → R),
    Crd (O1.pull (P.hom ⁻¹ᵁ W l).ι) (σ l) x w →
    Crd O1 st (x ≫ (P.hom ⁻¹ᵁ W l).ι) (((c l).map (valR (x ≫ (P.hom ⁻¹ᵁ W l).ι ≫ P.hom) (W l))).mulVec w)
  imm : ∀ l, ImmBy (k := Γ(M.Z, W l)) ((P.hom ∣_ W l) ≫ (aff l).isoSpec.hom) (O1.pull (P.hom ⁻¹ᵁ W l).ι) (σ l) Set.univ
attribute [instance] Clos.intP
namespace Clos
variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Q : Clos ρ M U₀ EE)

def G : Q.P.left.Opens :=
  ⨆ (z : M.Z) (_ : IsClosed ({z} : Set M.Z)) (W : M.Z.Opens) (_ : ∀ z' ∈ W, S.supI M z ⊆ S.supI M z') (i : S.J)
    (φ : Q.O1.Sec) (_ : IsLin (Q.P.hom ≫ M.s) Q.st (fun j => S.proj (S.TT M z) 0 j i) φ),
    Q.P.hom ⁻¹ᵁ W ⊓ nonzeroLocus φ

structure Ext where
  π : M.Z ⟶ Sp ℤ
  flat : Flat π
  lft : LocallyOfFiniteType π
  qc : QuasiCompact π
  sep : IsSeparated π
  normal : IsNormalScheme M.Z
  ne : (U₀ : Set M.Z).Nonempty
  ab : IsAbelianScheme ((Over.pullback Q.u₀).obj ρ.P.A)
  dim : SmoothOfRelativeDimension S.g ((Over.pullback Q.u₀).obj ρ.P.A).hom
  a : pullback ρ.P.A.hom Q.u₀ ⟶ Q.G.toScheme
  a_eq : a ≫ Q.G.ι = Q.a₀
  e : M.Z ⟶ Q.G.toScheme
  e_sec : e ≫ Q.G.ι ≫ Q.P.hom = 𝟙 M.Z
  e_zero : U₀.ι ≫ e = (eSec ((Over.pullback Q.u₀).obj ρ.P.A) ≫ a : U₀.toScheme ⟶ Q.G.toScheme)

def Ext.core {Q : Clos ρ M U₀ EE} (x : Q.Ext) : GlobalTheory.ZJ.Core where
  Z := M.Z
  π := x.π
  flat := x.flat
  lft := x.lft
  qc := x.qc
  sep := x.sep
  normal := x.normal
  U := U₀
  ne := x.ne
  g := S.g
  A := (Over.pullback Q.u₀).obj ρ.P.A
  comm := x.ab.comm
  ab := x.ab
  dim := x.dim
  P := Q.P
  proper := Q.proper
  G := Q.G
  a := x.a
  cart := by have := Q.cart; rw [← x.a_eq] at this; exact this
  e := x.e
  e_sec := x.e_sec
  e_zero := x.e_zero

def Tors {K : Type} [Field K] (t : Sp K ⟶ M.Z) (l : Q.Λ) : Set (S.J → K) :=
  {w | ∃ z ∈ Set.range t, ∃ x₀ ∈ S.supI M z, ∃ h ∈ S.HH M z, w = fun i => M.val t ((Q.B l i ⬝ᵥ S.ev h) / S.th x₀)}

def InFib {K : Type} [Field K] (x : Sp K ⟶ Q.P.left) : Prop :=
  ∀ (l : Q.Λ) (x' : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (w : S.J → K), x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x →
    Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x' w → ∀ (d : ℕ) (Pf : MvPolynomial S.J K),
      d ≤ S.N ^ S.g * S.g.factorial → Pf.IsHomogeneous d →
      (∀ v ∈ Q.Tors (x ≫ Q.P.hom) l, MvPolynomial.eval v Pf = 0) → MvPolynomial.eval w Pf = 0

structure Fac {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) where
  at_ : S.At M y y₀
  yV : Sp u.V ⟶ M.Z
  fac : spMap u.j ≫ yV = y
  yK : Sp (FractionRing u.V) ⟶ U₀.toScheme
  yK_fac : yK ≫ U₀.ι = jK u.V ≫ yV
  yK_u : yK ≫ Q.u₀ = spMap u.yK

structure TMap {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} (t : ρ.GeoTest p y₀)
    (c : Q.Fac y t.u) where
  l : Q.Λ
  mem : y (cPt p) ∈ Q.W l
  m : Matrix S.J S.J t.u.V
  unit : IsUnit m.det
  m_eq : (Q.B l).map (M.val (gPt p ≫ y)) =
    (m.map fun a => (t.u.j a : PadicAlgCl p)) * t.b.map (algebraMap _ (PadicAlgCl p))
  f : t.u.G.left ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme
  f_over : f ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t.u.G.hom ≫ c.yV
  φ : pullback t.u.G.hom (jK t.u.V) ⟶ pullback ρ.P.A.hom Q.u₀
  φ_fst : φ ≫ pullback.fst _ _ = t.u.U.gen.hom.left ≫ t.u.φ
  φ_snd : φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ c.yK
  φ_f : φ ≫ Q.a₀ = pullback.fst _ _ ≫ f ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι
  crd : ∀ (R : Type) [CommRing R] [IsLocalRing R] (ψ : t.u.V →+* R) (x : Sp R ⟶ t.u.G.left) (w : S.J → R),
    x ≫ t.u.G.hom = spMap ψ → Crd (t.u.H S.N) t.σ x w →
    Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) (x ≫ f) ((m.map ψ).mulVec w)
end Clos

structure BaseFacts (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) : Prop where
  ov : S.Over₀ M U₀
  ee : S.IsEE M U₀ EE
  jac : JacobsonSpace M.Z
  atTest : ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀),
    M.Cen U₀ z y → S.At M y y₀ → S.HH M z = τ.yy.ker
  free : ∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ
  gen : ∀ ξ ∈ U₀, S.TT M ξ = ⊥
  mem : ∀ ξ i, Pi.single i (1 : Ω) ∈ EE.E ξ
  stab : ∀ ξ, ∀ h ∈ S.HH M ξ, ∀ v ∈ EE.E ξ, ((S.ρ h).map (algebraMap o Ω)).mulVec v ∈ EE.E ξ
  zero : ∀ ξ, IsClosed ({ξ} : Set M.Z) → ∀ v ∈ EE.E ξ,
    ((S.proj (S.TT M ξ) 0).map (algebraMap o Ω)).mulVec v = v → ∀ j, v j ∈ M.O ξ
  sec : ∀ ξ : M.Z, ∀ x₀ ∈ S.supI M ξ, ∀ h ∈ S.HH M ξ, (∀ v ∈ EE.E ξ, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O ξ) ∧
    ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧
      S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O ξ
end GlobalTheory.ZH
end
end
