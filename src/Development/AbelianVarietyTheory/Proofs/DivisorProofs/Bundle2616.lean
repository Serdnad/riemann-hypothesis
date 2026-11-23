module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.RankZero

theorem eq_zero_of_half_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [hd : DiscreteTopology Λ]
    (h : ∀ z ∈ Λ, (2⁻¹ : ℝ) • z ∈ Λ) (z : Fin g → ℂ) (hz : z ∈ Λ) : z = 0 := by
  have hn : ∀ n : ℕ, ((2⁻¹ : ℝ) ^ n) • z ∈ Λ := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih => rw [pow_succ', mul_smul]; exact h _ ih
  have ht : Filter.Tendsto (fun n : ℕ => ((2⁻¹ : ℝ) ^ n) • z) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)).smul_const z
    simpa using this
  have ht' : Filter.Tendsto (fun n : ℕ => (⟨_, hn n⟩ : Λ)) Filter.atTop (nhds 0) :=
    tendsto_subtype_rng.2 ht
  rw [nhds_discrete, Filter.tendsto_pure] at ht'
  obtain ⟨n, hn'⟩ := ht'.exists
  have h0 : ((2⁻¹ : ℝ) ^ n) • z = 0 := congrArg Subtype.val hn'
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 (by positivity)
  · exact h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem subsingleton_lattice (D : Datum H) (hD : D.p + D.q = 0) : Subsingleton D.La := by
  haveI := D.fin
  haveI := D.proj
  by_contra hne
  have hnt : Nontrivial D.La := not_subsingleton_iff_nontrivial.1 hne
  have := (Module.finrank_pos_iff (R := 𝓞 E) (M := D.La)).2 hnt
  rw [D.rank, hD] at this
  exact lt_irrefl _ this

theorem subsingleton_unif {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {s : Sp ℂ ⟶ Sp B}
    (hD : D.p + D.q = 0) (o : Obj D l b s) {g : ℕ} (u : HolUnif o.t.G o.t.PP.L g) :
    Subsingleton (Fin g → ℂ) := by
  haveI := subsingleton_lattice D hD
  obtain ⟨-, I, -⟩ := o.geom ℂ (𝟙 _) (Spec.preimage s).hom (by simp [spMap])
  have h1 : I.ev 2 0 = 1 := (I.ker 2 two_pos 0).2 ⟨0, Subsingleton.elim _ _⟩
  have htor : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x * x = 1 → x = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := (I.onto 2 two_pos x).1 (by rw [pow_two]; exact hx)
    rw [Subsingleton.elim a 0, h1] at ha
    exact ha.symm
  haveI := u.discrete
  have hΛ : ∀ z ∈ u.Λ, z = 0 := by
    refine eq_zero_of_half_mem u.Λ (fun z hz => (u.ker _).1 (htor _ ?_))
    rw [← u.ex_add, ← add_smul, u.ker]
    norm_num
    exact hz
  refine subsingleton_of_forall_eq 0 (fun z => ?_)
  have hz : z ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) := by rw [u.full]; trivial
  have : Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) = ⊥ := Submodule.span_eq_bot.2 hΛ
  rwa [this, Submodule.mem_bot] at hz

theorem hasTransport_of_rank_zero (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l)
    (U : Set (Xo.XF c)) (e : c.F →+* ℂ) (hD : D.p + D.q = 0) : HasTransport Xo c U e := by
  intro y y' _ _ _ _ o o' _ _ g g' u u' Hm Hm' κ κ' _ _
  haveI := subsingleton_unif hD o u
  haveI := subsingleton_unif hD o' u'
  haveI : Subsingleton (𝟙_ (Over (Sp ℂ)) ⟶ o'.t.G) := u'.ex_onto.subsingleton
  refine ⟨LinearEquiv.ofSubsingleton _ _, fun z => ?_, fun _ _ _ _ => Subsingleton.elim _ _, fun z w => ?_,
    fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  · rw [Subsingleton.elim z 0, map_zero]
    simp
  · rw [Subsingleton.elim z 0, map_zero]
    simp [HermitianCompactForm.herm]

end GlobalTheory.DetLine.RankZero
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.WedgeCoord

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

def hl (w : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun z := herm Hm z w
  map_add' x y := by simp [herm, add_dotProduct]
  map_smul' c x := by simp [herm, smul_dotProduct]

theorem hl_apply (w z : Fin g → ℂ) : hl Hm w z = herm Hm z w := rfl

theorem herm_add_right (z w w' : Fin g → ℂ) : herm Hm z (w + w') = herm Hm z w + herm Hm z w' := by
  simp [herm, Matrix.mulVec_add, dotProduct_add]

theorem herm_smul_right (z w : Fin g → ℂ) (c : ℂ) : herm Hm z (c • w) = star c * herm Hm z w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

theorem herm_zero_right (z : Fin g → ℂ) : herm Hm z 0 = 0 := by
  simp [herm]

theorem herm_eq_zero_of_mem_span {s : Set (Fin g → ℂ)} {z w : Fin g → ℂ}
    (h : ∀ v ∈ s, herm Hm z v = 0) (hw : w ∈ Submodule.span ℂ s) : herm Hm z w = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact herm_zero_right Hm z
  | add x y _ _ hx hy => rw [herm_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [herm_smul_right, hx, mul_zero]

theorem herm_symm (hH : Hm.IsHermitian) (z w : Fin g → ℂ) : herm Hm z w = star (herm Hm w z) := by
  unfold herm
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq,
    Matrix.dotProduct_mulVec]

theorem gram_surj (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) {n : Type} [Fintype n]
    (V : n → Fin g → ℂ) (hV : LinearIndependent ℂ V) (c : n → ℂ) :
    ∃ a : n → ℂ, ∀ i, herm Hm (∑ m, a m • V m) (V i) = c i := by
  classical
  let T : (n → ℂ) →ₗ[ℂ] (n → ℂ) :=
    (LinearMap.pi fun i => hl Hm (V i)) ∘ₗ Fintype.linearCombination ℂ V
  have hT : ∀ a i, T a i = herm Hm (∑ m, a m • V m) (V i) := fun a i => rfl
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h0 : ∑ m, a m • V m = 0 := by
      by_contra hne
      have h1 := hpos _ hne
      have h2 : herm Hm (∑ m, a m • V m) (∑ m, a m • V m) = 0 := by
        refine herm_eq_zero_of_mem_span Hm (s := Set.range V) ?_ ?_
        · rintro _ ⟨i, rfl⟩
          rw [← hT, ha]; rfl
        · exact Submodule.sum_mem _ fun m _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      rw [h2] at h1
      simp at h1
    funext i
    exact Fintype.linearIndependent_iff.1 hV a h0 i
  obtain ⟨a, ha⟩ := LinearMap.surjective_of_injective hinj c
  exact ⟨a, fun i => by rw [← hT, ha]⟩

theorem exists_proj (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) {p : ℕ}
    (V : Fin p → Fin g → ℂ) (y : Fin g → ℂ) :
    ∃ a : Fin p → ℂ, ∀ i, herm Hm (y - ∑ m, a m • V m) (V i) = 0 := by
  classical
  obtain ⟨s, hsV, hspan, hli⟩ := exists_linearIndependent ℂ (Set.range V)
  have hfin : s.Finite := (Set.finite_range V).subset hsV
  haveI := hfin.fintype
  obtain ⟨c, hc⟩ := gram_surj Hm hpos (fun v : s => (v : Fin g → ℂ)) hli (fun v => herm Hm y v)
  have hmem : ∑ m : s, c m • (m : Fin g → ℂ) ∈ Submodule.span ℂ (Set.range V) :=
    Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span (hsV m.2))
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨a, fun i => ?_⟩
  rw [ha]
  refine herm_eq_zero_of_mem_span Hm (s := s) ?_ ?_
  · intro v hv
    rw [← hl_apply, map_sub, hl_apply, hl_apply, hc ⟨v, hv⟩, sub_self]
  · rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩

end GlobalTheory.DetLine.WedgeCoord

open GlobalTheory.DetLine.WedgeCoord in
theorem GlobalTheory.DetLine.exists_wedgeCoord : ∀ (g p q : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) → (∀ x, ∃ Δ, IsWedgeCoord Hm V W x Δ) ∧ (LinearIndependent ℂ V → LinearIndependent ℂ W → ∃ x Δ, Δ ≠ 0 ∧ IsWedgeCoord Hm V W x Δ) := by
  intro g p q Hm V W hH hpos
  refine ⟨fun x => ?_, fun hV hW => ?_⟩
  · choose a ha using fun k => exists_proj Hm hpos V (x k)
    exact ⟨_, a, ha, rfl⟩
  · classical
    let P : Type := {z : (Fin g → ℂ) × (Fin p → ℂ) //
      ∀ i, herm Hm (z.1 - ∑ m, z.2 m • V m) (V i) = 0}
    let r : P → (Fin q ⊕ Fin p → ℂ) := fun z =>
      Sum.elim (fun j => -(Real.pi : ℂ) * herm Hm (W j) z.1.1) (fun i => z.1.2 i)
    have key : ∀ z : P, Sum.elim (fun j => -(Real.pi : ℂ) * herm Hm (W j) z.1.1) (0 : Fin p → ℂ) ∈
        Submodule.span ℂ (Set.range r) ∧
        Sum.elim (0 : Fin q → ℂ) z.1.2 ∈ Submodule.span ℂ (Set.range r) := by
      intro z
      let z' : P := ⟨(Complex.I • z.1.1, Complex.I • z.1.2), fun i => by
        have : Complex.I • z.1.1 - ∑ m, (Complex.I • z.1.2) m • V m =
            Complex.I • (z.1.1 - ∑ m, z.1.2 m • V m) := by
          simp only [smul_sub, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, mul_smul]
        show herm Hm (Complex.I • z.1.1 - ∑ m, (Complex.I • z.1.2) m • V m) (V i) = 0
        rw [this, ← hl_apply, map_smul, hl_apply, z.2 i, smul_zero]⟩
      have h1 : r z ∈ Submodule.span ℂ (Set.range r) := Submodule.subset_span ⟨z, rfl⟩
      have h2 : r z' ∈ Submodule.span ℂ (Set.range r) := Submodule.subset_span ⟨z', rfl⟩
      have hI := Complex.I_mul_I
      constructor
      · convert Submodule.smul_mem _ (1/2 : ℂ) (Submodule.add_mem _ h1
          (Submodule.smul_mem _ Complex.I h2)) using 1
        funext k
        rcases k with j | i
        · simp only [r, z', Sum.elim_inl, Pi.smul_apply, Pi.add_apply, smul_eq_mul, herm_smul_right,
            Complex.star_def, Complex.conj_I]
          linear_combination (-(1/2) * (Real.pi : ℂ) * herm Hm (W j) z.1.1) * hI
        · simp only [r, z', Sum.elim_inr, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply]
          linear_combination (-(1/2) * z.1.2 i) * hI
      · convert Submodule.smul_mem _ (1/2 : ℂ) (Submodule.sub_mem _ h1
          (Submodule.smul_mem _ Complex.I h2)) using 1
        funext k
        rcases k with j | i
        · simp only [r, z', Sum.elim_inl, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, herm_smul_right,
            Complex.star_def, Complex.conj_I, Pi.zero_apply]
          linear_combination ((1/2) * (Real.pi : ℂ) * herm Hm (W j) z.1.1) * hI
        · simp only [r, z', Sum.elim_inr, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          linear_combination ((1/2) * z.1.2 i) * hI
    have hspan : Submodule.span ℂ (Set.range r) = ⊤ := by
      rw [eq_top_iff]
      intro u _
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      obtain ⟨c, hc⟩ := gram_surj Hm hpos W hW (fun j => star (u (Sum.inl j) / (-(Real.pi : ℂ))))
      obtain ⟨a, ha⟩ := exists_proj Hm hpos V (∑ m, c m • W m)
      have h1 := (key ⟨(∑ m, c m • W m, a), ha⟩).1
      have h2 := (key ⟨(∑ m, u (Sum.inr m) • V m, fun m => u (Sum.inr m)), fun i => by
        simp [herm]⟩).2
      convert Submodule.add_mem _ h1 h2 using 1
      funext k
      rcases k with j | i
      · simp only [Sum.elim_inl, Pi.add_apply, Pi.zero_apply, add_zero]
        rw [herm_symm Hm hH, hc, star_star]
        field_simp
      · simp
    by_contra hcon
    push_neg at hcon
    have hz : (Matrix.detRowAlternating (n := Fin q ⊕ Fin p) (R := ℂ)).toMultilinearMap = 0 := by
      refine MultilinearMap.ext_of_span_eq_top (g := fun _ => r) (fun _ => hspan) fun s => ?_
      by_contra hne
      exact hcon (fun k => (s k).1.1) _ hne ⟨fun k => (s k).1.2, fun k => (s k).2, rfl⟩
    have := congrArg (fun f => f (1 : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ)) hz
    have h1 : Matrix.det (1 : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) = 0 := this
    simp at h1
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

theorem _root_.GlobalTheory.T.hasMarkingPreservingTransport_of_conj_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ), HasTransport Xo c U ((starRingEnd ℂ).comp e) → HasTransport Xo c U e := by
  first | exact @GlobalTheory.hasTransport_of_conj | exact GlobalTheory.hasTransport_of_conj | (intros; apply GlobalTheory.hasTransport_of_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem isIntegral_open_of_geometricallyConnected :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H)
      (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens),
      GeometricallyConnected (U.ι ≫ toF Xo c) → IsIntegral U.toScheme := by
  intro E _ _ _ H D l Xo c U hU
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth (toF Xo c) := inferInstanceAs (Smooth (pullback.snd _ _))
  have : ConnectedSpace U.toScheme :=
    GeometricallyConnected.connectedSpace_of_subsingleton (U.ι ≫ toF Xo c)
  exact GlobalTheory.isIntegral_of_smooth_field (U.ι ≫ toF Xo c)

end GlobalTheory.DetLine
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.OneValue

theorem isAlgebraic_of_one_value {F A C : Type} [Field F] [CommRing A] [Nontrivial A] [IsReduced A] [Algebra F A]
    [Algebra.FiniteType F A] [Field C] [IsAlgClosed C] [Algebra F C] (s : A)
    (h : ∀ φ ψ : A →ₐ[F] C, φ s = ψ s) : IsAlgebraic F s := by
  have hJ : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := F)
  have key : ∀ m : Ideal A, m.IsMaximal →
      ∃ φ : A →ₐ[F] C, (∀ a, φ a = 0 → a ∈ m) ∧ IsAlgebraic F (φ s) := by
    intro m hm
    letI := Ideal.Quotient.field m
    have : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
    let σ : (A ⧸ m) →ₐ[F] C := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨σ.comp (Ideal.Quotient.mkₐ F m), fun a ha => ?_, ?_⟩
    · exact Ideal.Quotient.eq_zero_iff_mem.1 (σ.toRingHom.injective (ha.trans (map_zero σ.toRingHom).symm))
    · exact (Algebra.IsAlgebraic.isAlgebraic (R := F) (Ideal.Quotient.mkₐ F m s)).algHom σ
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A
  obtain ⟨φ₀, -, P, hP, hPs⟩ := key m₀ hm₀
  refine ⟨P, hP, ?_⟩
  have hj : Polynomial.aeval s P ∈ (⊥ : Ideal A).jacobson := by
    refine Ideal.mem_sInf.2 ?_
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ, -⟩ := key m hm
    refine hφ _ ?_
    rw [← Polynomial.aeval_algHom_apply, h φ φ₀, hPs]
  rwa [hJ.out (Ideal.isRadical_bot_iff.2 inferInstance), Ideal.mem_bot] at hj

theorem valR_spMap_fromSpec {X : Scheme.{0}} {R : Type} [CommRing R] {U W : X.Opens} (hW : IsAffineOpen W)
    (e : W ≤ U) (φ : Γ(X, W) →+* R) (f : Γ(X, U)) :
    valR (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X) U f = φ (resG X e f) := by
  have h0 : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W := hW.fromSpec_preimage_self.ge
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X) ⁻¹ᵁ U :=
    fun y _ => e (h0 (Set.mem_univ ((Spec.map (CommRingCat.ofHom φ)) y)))
  unfold valR
  rw [dite_eq_left h]
  have e1 : (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X).appLE U ⊤ h =
      X.presheaf.map (homOfLE e).op ≫ hW.fromSpec.appLE W ⊤ h0 ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    rw [← Category.assoc, Scheme.Hom.map_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ _ le_rfl).symm
  have e2 : hW.fromSpec.appLE W ⊤ h0 = (Scheme.ΓSpecIso Γ(X, W)).inv := by
    rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) ((Spec Γ(X, W)).presheaf.map_id _)).trans (Category.comp_id _)
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change ((Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X).appLE U ⊤ h ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom f =
    (X.presheaf.map (homOfLE e).op ≫ CommRingCat.ofHom φ).hom f
  rw [e1, e2, Category.assoc, Category.assoc]
  erw [n]
  erw [(Scheme.ΓSpecIso Γ(X, W)).inv_hom_id_assoc]

theorem exists_eq_algX {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [GeometricallyIntegral p]
    [LocallyOfFiniteType p] (e : F →+* ℂ) (f : Γ(Y, ⊤))
    (h : ∀ y y' : Sp ℂ ⟶ Y, y ≫ p = spMap e → y' ≫ p = spMap e → valR y ⊤ f = valR y' ⊤ f) :
    ∃ a : F, f = algX p ⊤ a := by
  have : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton p
  obtain ⟨U, hU, hxU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have hc : (algX p U).FiniteType := by
    have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2)
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have : Algebra.FiniteType F Γ(Y, U) := hc
  letI : Algebra F ℂ := e.toAlgebra
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(Y, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hpt : ∀ φ : Γ(Y, U) →ₐ[F] ℂ,
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec : Sp ℂ ⟶ Y) ≫ p = spMap e := by
    intro φ
    rw [Category.assoc, hg, ← Spec.map_comp]
    congr 1
    ext a
    exact φ.commutes a
  obtain ⟨P, hP, hPs⟩ := isAlgebraic_of_one_value (F := F) (C := ℂ) (resG Y hUV f) fun φ ψ => by
    have := h _ _ (hpt φ) (hpt ψ)
    rwa [valR_spMap_fromSpec hU hUV, valR_spMap_fromSpec hU hUV] at this
  obtain ⟨a, ha⟩ := GlobalTheory.GeomIntConst.mem_range_constFn F Y p (GlobalTheory.Cartier.fnOf ⊤ trivial f) ⟨P, hP, by
    rw [← GlobalTheory.Cartier.fnOf_comp_algX p U hxU, ← GlobalTheory.Cartier.fnOf_resG hUV hxU, ← Polynomial.hom_eval₂]
    exact (congrArg _ hPs).trans (map_zero _)⟩
  exact ⟨a, (GlobalTheory.Cartier.fnOf_injective ⊤ trivial ha).symm⟩

theorem exists_eq_constFn_of_one_value :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (f : Γ(Xo.XF c, U)), GeometricallyConnected (U.ι ≫ toF Xo c) → (∀ y y' : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e → Set.range y ⊆ U → Set.range y' ⊆ U → valR y U f = valR y' U f) → ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (toF Xo c) U a := by
  intro E _ _ _ H D l Xo c U e f hU h
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth (toF Xo c) := inferInstanceAs (Smooth (pullback.snd _ _))
  have : GeometricallyIntegral (U.ι ≫ toF Xo c) := GlobalTheory.geometricallyIntegral_of_smooth _
  have hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun x _ => x.2
  have hval : ∀ y : Sp ℂ ⟶ U.toScheme, valR y ⊤ ((U.ι.appLE U ⊤ hle).hom f) = valR (y ≫ U.ι) U f := by
    intro y
    have h1 : ⊤ ≤ y ⁻¹ᵁ ⊤ := le_top
    have h2 : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := fun x _ => (y x).2
    unfold valR
    rw [dite_eq_left h1, dite_eq_left h2, ← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ hle h1]
    rfl
  have hr : ∀ y : Sp ℂ ⟶ U.toScheme, Set.range (y ≫ U.ι) ⊆ U := by
    rintro y _ ⟨x, rfl⟩
    exact (y x).2
  obtain ⟨a, ha⟩ := exists_eq_algX (U.ι ≫ toF Xo c) e ((U.ι.appLE U ⊤ hle).hom f) fun y y' hy hy' => by
    rw [hval, hval]
    exact h _ _ ((Category.assoc _ _ _).trans hy) ((Category.assoc _ _ _).trans hy') (hr y) (hr y')
  refine ⟨a, ?_⟩
  have hiso : IsIso (U.ι.appLE U ⊤ hle) := by
    rw [Scheme.Opens.ι_appLE]
    have : U.ι ''ᵁ ⊤ = U := U.ι_image_top
    have : IsIso (homOfLE (x := U.ι ''ᵁ ⊤) (y := U) this.le) := ⟨homOfLE this.ge, rfl, rfl⟩
    exact Functor.map_isIso _ (homOfLE (x := U.ι ''ᵁ ⊤) (y := U) U.ι_image_top.le).op
  refine (ConcreteCategory.bijective_of_isIso (U.ι.appLE U ⊤ hle)).1 (ha.trans ?_)
  have := Scheme.Hom.appLE_comp_appLE U.ι (toF Xo c) ⊤ U ⊤ (fun _ _ => trivial) hle
  exact (congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a)) this).symm

end GlobalTheory.OneValue
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_generatingFrame_unit_change_to_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : GChart Y) (V K : Type) [CommRing V] [IsLocalRing V] [Field K] [CharZero K] [Algebra V K] (yt : Sp V ⟶ Y.X) (hz : ⊤ ≤ yt ⁻¹ᵁ M.U) (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)), IsLieBasis w → ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) → Generates (X := t.G) θ → ∃ (x' : KeyIn K) (a d : Vˣ), KeyAt M (spMap (algebraMap V K) ≫ yt) (le_preimage_comp _ hz) x' ∧ ∀ κ : KeyRule, IsKeyRule κ → algebraMap V K a ^ 8 * (κ K x' : K) = algebraMap V K d ^ 4 * (κ K x : K) := by
  first | exact @GlobalTheory.KeyFramePoint.exists_keyAt_units | exact GlobalTheory.KeyFramePoint.exists_keyAt_units | (intros; apply GlobalTheory.KeyFramePoint.exists_keyAt_units <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.exists_weilRep_dualPair_characters_beta_quotient : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (r s r' s' : ℕ), X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∃ om, Mo.IsWeil B.ψ (beta G i j) (beta G i j / alpha G t i j) om := by
  first | exact @GlobalTheory.WeilTripleW.exists_isWeil | exact GlobalTheory.WeilTripleW.exists_isWeil | (intros; apply GlobalTheory.WeilTripleW.exists_isWeil <;> assumption)
end
