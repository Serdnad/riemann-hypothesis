module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle030
public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LimitIdempotentRangeLeSumEigenspaces
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hopfPoint_mem {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [Unique N] (f : N → C) (hf : f ∈ L2.intFun (C := C) R N) :
    ∃ r : R, f = r • (1 : N → C) := by
  obtain ⟨r, hr⟩ := hf default
  refine ⟨r, funext fun x => ?_⟩
  rw [Subsingleton.elim x default, ← hr]
  simp [Algebra.smul_def]

private theorem hopfPoint_one {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) : (1 : N → C) ∈ L2.intFun (C := C) R N := fun _ => ⟨1, by simp⟩

private def hopfPoint {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] [Unique N] :
    L2.HopfOrder (C := C) R N where
  carrier := L2.intFun R N
  lat := by
    refine ⟨1, by simp, le_antisymm ?_ ?_⟩
    · intro f hf
      obtain ⟨r, rfl⟩ := hopfPoint_mem R N f hf
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨default, ?_⟩)
      funext x
      rw [Subsingleton.elim x default]
      simp
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩ x
      refine ⟨1, ?_⟩
      rw [Subsingleton.elim x j]
      simp
  le_int := le_rfl
  one_mem := hopfPoint_one R N
  mul_mem := by
    intro f g hf hg x
    obtain ⟨r, hr⟩ := hf x
    obtain ⟨s, hs⟩ := hg x
    exact ⟨r * s, by simp [hr, hs]⟩
  comul := by
    intro f hf
    refine Submodule.subset_span ⟨f, hf, 1, hopfPoint_one R N, ?_⟩
    funext q
    change f (q.1 + q.2) = f q.1 * 1
    rw [_root_.mul_one, Subsingleton.elim (q.1 + q.2) q.1]
  antipode := fun f hf x => hf (-x)

theorem htd_dim_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (cp : O), Nonempty (HodgeTateDatum p 0 v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ OE _ _ cp
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  have hS : Subsingleton (LieDualModP p O 0) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  refine ⟨{
    ρ :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _
        commutes' := fun _ => Subsingleton.elim _ _ }
    ρL :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    P := 0
    PL := 0
    E := 0
    E_alternating := ⟨Subsingleton.elim _ _, fun _ => rfl⟩
    isUnit_det_E := by simp
    E_equivariant := fun _ => Subsingleton.elim _ _
    projectors := ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
    Ht := 0
    Bt := 0
    Ht_equivariant := ⟨fun _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    form_eq_alt := Subsingleton.elim _ _
    AA := hopfPoint O (Nb p 0)
    h3 := fun a f hf => ⟨f, hf, fun t => congrArg f (Subsingleton.elim _ _)⟩
    h4 := fun k => k.elim0
    h5 := fun _ s => ⟨1, hopfPoint_one O _, fun t => by
      have h0 : Up.pair p 0 0 s t = 0 := by simp [Up.pair]
      rw [h0, map_zero, ZMod.val_zero, pow_zero, Pi.one_apply]⟩
    φ := 0
    cotangent_surjective := fun y => ⟨0, Subsingleton.elim _ _⟩
    cotangent_ker_eq := ?_
    cotangent_linear := fun _ _ _ _ _ _ => Subsingleton.elim _ _ }⟩
  rw [LinearMap.ker_zero, eq_comm, eq_top_iff]
  intro f _
  have : f = 0 := by
    apply Subtype.ext
    funext x
    rw [Subsingleton.elim x 0]
    exact f.2.2
  rw [this]
  exact Submodule.zero_mem _

end GlobalTheory.ChF
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChF
open MvPowerSeries

private lemma gm_hs {R : Type} [CommRing R] {m n d : ℕ} (a : Fin m → Pt R n d)
    (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero (fun p => h p.1 p.2)

private lemma ev_gm {R : Type} [CommRing R] {n r : ℕ} (a b : Pt R n r)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin r) :
    ev ![a, b] (gmF R r i) = a i + b i + a i * b i := by
  have h := gm_hs (m := 2) ![a, b] (by
    intro j i
    fin_cases j
    · exact ha i
    · exact hb i)
  unfold ev gmF
  rw [subst_add h, subst_add h, subst_mul h, subst_X h, subst_X h]
  rfl

private lemma ev_ch {R : Type} [CommRing R] {n r : ℕ} (a : Pt R n r)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin r) :
    ev ![a] (1 + X ((0 : Fin 1), i) : PS R 1 r) = 1 + a i := by
  have h := gm_hs (m := 1) ![a] (by
    intro j i
    fin_cases j
    exact ha i)
  have h1 := ev_one ![a]
  unfold ev at h1 ⊢
  rw [subst_add h, h1, subst_X h]
  rfl

private lemma gm_const {R : Type} [CommRing R] {r : ℕ} (i : Fin r) :
    constantCoeff (gmF R r i) = 0 := by
  simp [gmF]

private lemma pt_const {R : Type} [CommRing R] {n r : ℕ} (j : Fin n) (i : Fin r) :
    constantCoeff (pt R r j i) = 0 := by
  simp [pt]

private def gmLaw (R : Type) [CommRing R] (r : ℕ) : FGLaw R r where
  F := gmF R r
  const := gm_const
  unit i := by
    rw [ev_gm _ _ (by simp) (pt_const _)]
    simp [pt]
  comm i := by
    rw [ev_gm _ _ (pt_const _) (pt_const _)]
    simp only [pt, gmF]
    ring
  assoc i := by
    have h : ∀ (j k : Fin 3) (l : Fin r), constantCoeff (ev (n := 3) ![pt R r j, pt R r k] (gmF R r l)) = 0 := by
      intro j k l
      rw [ev_gm _ _ (pt_const _) (pt_const _)]
      simp [pt]
    rw [ev_gm _ _ (h _ _) (pt_const _), ev_gm _ _ (pt_const _) (h _ _),
      ev_gm _ _ (pt_const _) (pt_const _), ev_gm _ _ (pt_const _) (pt_const _)]
    ring

private lemma mulF_gm (R : Type) [CommRing R] (r : ℕ) (N : ℕ) :
    ∀ i : Fin r, mulF (gmF R r) N i = (1 + X ((0 : Fin 1), i)) ^ N - 1 := by
  induction N with
  | zero => intro i; simp [mulF]
  | succ N ih =>
    intro i
    simp only [mulF, addOf]
    rw [ev_gm _ _ (by intro l; rw [ih]; simp) (pt_const _), ih]
    simp only [pt]
    ring

theorem gmLaw_chars_mul : ∀ (R : Type) [CommRing R] (r : ℕ), (∃ Gl : FGLaw R r, Gl.F = gmF R r) ∧ (∀ i : Fin r, IsCh (gmF R r) (1 + MvPowerSeries.X ((0 : Fin 1), i)) ∧ dl (1 + MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 r) = Pi.single i 1) ∧ ∀ (N : ℕ) (i : Fin r), mulF (gmF R r) N i = (1 + MvPowerSeries.X ((0 : Fin 1), i)) ^ N - 1 := by
  intro R _ r
  refine ⟨⟨gmLaw R r, rfl⟩, fun i => ⟨⟨by simp, ?_⟩, ?_⟩, mulF_gm R r⟩
  · have hA : addOf (gmF R r) (pt R (n := 2) r 0) (pt R (n := 2) r 1) = gmF R r := by
      funext l
      unfold addOf
      rw [ev_gm _ _ (pt_const _) (pt_const _)]
      rfl
    rw [hA, ev_ch _ gm_const, ev_ch _ (pt_const _), ev_ch _ (pt_const _)]
    simp only [pt, gmF]
    ring
  · classical
    funext j
    simp only [dl, map_add (f := _), coeff_one, coeff_X, Finsupp.single_eq_zero, one_ne_zero, if_false, zero_add,
      Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), Prod.mk.injEq, true_and, Pi.single_apply]

end GlobalTheory.ChF
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_comp_single {R : Type} [CommRing R] {d : ℕ} (φ ψ : Pt R 1 d)
    (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) : lin (comp1 φ ψ) = lin φ * lin ψ := by
  ext i j
  have h := coeff_lin_ev (m := 1) ![ψ] (by intro k l; fin_cases k; exact hψ l) (φ i) (0, j)
  rw [Fintype.sum_prod_type, Fin.sum_univ_one] at h
  rw [Matrix.mul_apply]
  exact h

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_formal_add {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (φ ψ : Pt R 1 d)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) : lin (F.add φ ψ) = lin φ + lin ψ := by
  ext i j
  have h := coeff_lin_ev (m := 2) ![φ, ψ]
    (by intro k l; fin_cases k; exacts [hφ l, hψ l]) (F.F i) (0, j)
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [formal_group_coeff_first_linear, formal_group_coeff_second_linear, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  exact h.trans (congrArg₂ (· + ·) (_root_.one_mul _) (_root_.one_mul _))

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_zero_point {R : Type} [CommRing R] {d : ℕ} : lin (pt R (n := 1) d 0) = 1 := by
  ext i j
  change MvPowerSeries.coeff _ (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 d) = _
  rw [coeff_X_single, Matrix.one_apply]
  simp [eq_comm]

theorem linPart_act_ringHom : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (OE : Type) [CommRing OE] (act : Geo.Tor.Germ.OAct OE F) (S : Type) [CommRing S] (β : R →+* S), ∃ ρ : OE →+* Matrix (Fin d) (Fin d) S, ∀ a, ρ a = linPart (actMap β act a) ∧ ρ a = (lin (act.act a)).map β := by
  intro R _ d F OE _ act S _ β
  let ρ₀ : OE →+* Matrix (Fin d) (Fin d) R := RingHom.mk'
    { toFun := fun a => lin (act.act a)
      map_one' := by rw [act.one_act, linear_part_zero_point]
      map_mul' := fun a b => by rw [act.mul_act, linear_part_comp_single _ _ (act.const b)] }
    (fun a b => by
      change lin (act.act (a + b)) = lin (act.act a) + lin (act.act b)
      rw [act.add_act, linear_part_formal_add _ _ _ (act.const a) (act.const b)])
  refine ⟨(β.mapMatrix).comp ρ₀, fun a => ⟨?_, rfl⟩⟩
  ext i j
  change β (MvPowerSeries.coeff _ (act.act a i)) =
    MvPowerSeries.coeff _ (MvPowerSeries.map β (act.act a i))
  rw [MvPowerSeries.coeff_map]

end GlobalTheory.ChF
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma smul_mem_span_of_split {O κ : Type} [CommRing O] [Fintype κ] [DecidableEq κ] {g d r m : ℕ}
    (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (Ht : Matrix (Fin g) κ O)
    (s : Fin m → Fin d → O) (cp : O) (hex : SplitEx A B)
    (hB : ∀ i, ∃ k, s k = Bᵀ *ᵥ (fun l => Ht l i)) (hT : ∀ i, ∃ k, Aᵀ *ᵥ s k = Pi.single i 1)
    (hsurj : ∀ f : Fin g → O, ∃ t, Ht *ᵥ t = cp • f) (f : Fin d → O) :
    cp • f ∈ Submodule.span O (Set.range s) := by
  obtain ⟨-, A', B', -, -, h1⟩ := hex
  choose k hk using hT
  set u : Fin d → O := ∑ i, (Aᵀ *ᵥ f) i • s (k i) with hu
  have huS : u ∈ Submodule.span O (Set.range s) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, rfl⟩)
  have hAu : Aᵀ *ᵥ u = Aᵀ *ᵥ f := by
    rw [hu, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hk]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h0 : Aᵀ *ᵥ (f - u) = 0 := by rw [Matrix.mulVec_sub, hAu, sub_self]
  have h2 : A'ᵀ * Aᵀ + Bᵀ * B'ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_add, h1, Matrix.transpose_one]
  have h3 : f - u = Bᵀ *ᵥ (B'ᵀ *ᵥ (f - u)) := by
    have := congrArg (fun M => M *ᵥ (f - u)) h2
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, zero_add,
      Matrix.one_mulVec] at this
    exact this.symm
  obtain ⟨t, ht⟩ := hsurj (B'ᵀ *ᵥ (f - u))
  have h4 : cp • (f - u) = Bᵀ *ᵥ (Ht *ᵥ t) := by rw [ht, Matrix.mulVec_smul, ← h3]
  have h5 : Ht *ᵥ t = ∑ i, t i • (fun l => Ht l i) := by
    ext l
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have h6 : cp • (f - u) ∈ Submodule.span O (Set.range s) := by
    rw [h4, h5, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    obtain ⟨j, hj⟩ := hB i
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj⟩)
  have h7 : cp • f = cp • (f - u) + cp • u := by rw [← smul_add, sub_add_cancel]
  rw [h7]
  exact Submodule.add_mem _ h6 (Submodule.smul_mem _ _ huS)

theorem linDat_hodgeTate_inclusion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ c : O, v (algebraMap O C c) ^ (p - 1) ≤ v (algebraMap O C (p : O)) → ∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range s) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H d r m A B ρG N s hL c hc f
  have := htd_domain hS
  obtain ⟨hEt, hdiag, hdet⟩ := htd_E H
  have hsurj := ht_cp_surj H.Ht H.Bt _ cp hEt hdiag hdet (htd_cp_ne hS) H.form_eq_alt
  have hle : v (algebraMap O C c) ≤ v (algebraMap O C cp) := by
    rw [← hS.cp_val] at hc
    exact le_of_pow_le_pow_left₀ (by have := (Fact.out : p.Prime).two_le; omega) zero_le hc
  obtain ⟨e, rfl⟩ := hv.dvd_of_le hle
  rw [mul_comm, mul_smul]
  exact Submodule.smul_mem _ _
    (smul_mem_span_of_split A B H.Ht s cp hL.exact hL.fromB hL.fromT hsurj f)

end GlobalTheory.ChF
end
end

section

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

private theorem mul_left_fst {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) {t : Z ⟶ S'} {r : Z ⟶ S}
    (x y : Over.mk t ⟶ (Over.pullback f).obj G) (x₀ y₀ : Over.mk r ⟶ G)
    (hx : x₀.left = x.left ≫ pullback.fst G.hom f) (hy : y₀.left = y.left ≫ pullback.fst G.hom f) :
    (x₀ * y₀).left = (x * y).left ≫ pullback.fst G.hom f := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  let z : Over.mk t ⟶ (Over.pullback f).obj (G ⊗ G) :=
    lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G
  have z₁ : z ≫ (Over.pullback f).map (fst G G) = x := by simp [z]
  have z₂ : z ≫ (Over.pullback f).map (snd G G) = y := by simp [z]
  have hz : (lift x₀ y₀).left = z.left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · show (lift x₀ y₀ ≫ fst G G).left = _ ≫ (fst G G).left
      rw [lift_fst, hx, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₁]
    · show (lift x₀ y₀ ≫ snd G G).left = _ ≫ (snd G G).left
      rw [lift_snd, hy, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₂]
  have hxy : x * y = z ≫ (Over.pullback f).map μ[G] := by
    rw [Hom.mul_def, Functor.obj.μ_def, ← Category.assoc]
  rw [hxy, Over.comp_left, Category.assoc, A, ← Category.assoc, ← hz]
  rfl

private theorem mono_thick (R : Type) [CommRing R] (I : Ideal R) (k : ℕ) : Mono (Out.thick R I k) := by
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem qRel_existsUnique_mul_nat : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G), (∀ (S : Type) [CommRing S] [Algebra R S], Kills I k S → (∀ z, ∃! y, QRel c S z y) ∧ ∀ z z' y y', QRel c S z y → QRel c S z' y' → QRel c S (z * z') (y * y')) ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') z y, QRel c S z y → QRel c S' (spMap φ ≫ z) (spMap φ ≫ y) := by
  intro R _ _ I D k G _ _ c
  have hm := mono_thick R I k
  have hf : Mono (pullback.fst G.hom (Out.thick R I k)) := inferInstance
  refine ⟨fun S _ _ hS => ?_, ?_⟩
  · let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
    have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    have hw : ∀ (z : sp (R₀ := R) S ⟶ G) (w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left),
        w ≫ (Out.fstG I k G).left = z.left → w ≫ (Out.thickObj R I k G).hom = t := by
      intro z w h
      rw [← cancel_mono (Out.thick R I k), ht]
      have h1 : (Out.thickObj R I k G).hom ≫ Out.thick R I k = (Out.fstG I k G).left ≫ G.hom :=
        (pullback.condition (f := G.hom) (g := Out.thick R I k)).symm
      rw [Category.assoc, h1, ← Category.assoc, h]
      exact Over.w z
    refine ⟨fun z => ?_, ?_⟩
    · let w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left :=
        pullback.lift z.left t ((Over.w z).trans ht.symm)
      have h1 : w ≫ (Out.fstG I k G).left = z.left := pullback.lift_fst _ _ _
      have h2 : (w ≫ c.pG.left) ≫ D.P.A.hom = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
        have h3 : c.pG.left ≫ D.P.A.hom = (Out.thickObj R I k G).hom ≫ Out.thick R I k := Over.w c.pG
        rw [Category.assoc, h3, ← Category.assoc, hw z w h1, ht]
      refine ⟨Over.homMk (w ≫ c.pG.left) h2, ⟨w, h1, rfl⟩, ?_⟩
      rintro y ⟨w', a, b⟩
      have e : w' = w := (cancel_mono (pullback.fst G.hom (Out.thick R I k))).1 (a.trans h1.symm)
      apply Over.OverMorphism.ext
      rw [← b, e]
      rfl
    · rintro z z' y y' ⟨w, a, b⟩ ⟨w', a', b'⟩
      have := c.q_hom
      let x : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w (hw z w a)
      let x' : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w' (hw z' w' a')
      refine ⟨(x * x').left, (mul_left_fst G (Out.thick R I k) x x' z z' a.symm a'.symm).symm, ?_⟩
      have e := mul_left_fst D.P.A (Out.thick R I k) (x ≫ c.q) (x' ≫ c.q) y y'
        (b.symm.trans (Category.assoc _ _ _).symm) (b'.symm.trans (Category.assoc _ _ _).symm)
      rw [← MonObj.mul_comp] at e
      exact ((Category.assoc _ _ _).symm.trans e.symm)
  · rintro S _ _ S' _ _ φ z y ⟨w, a, b⟩
    refine ⟨(spMap φ).left ≫ w, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans (congrArg ((spMap φ).left ≫ ·) a)
    · exact (Category.assoc _ _ _).trans (congrArg ((spMap φ).left ≫ ·) b)

end GlobalTheory.ChF
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (ι : Type) [Fintype ι] (e : ι → I → C) (z : I → ι → C) (al : I → ℕ → I → C), (∀ j x, e j x = ∑ b, z b j * S.tan b x) → (∀ c b, al c 0 b = if c = b then 1 else 0) → (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) → (∀ c, MvPowerSeries.constantCoeff (linPull e (t c)) = 0) ∧ (∀ (b : I) (μ : ι →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) = MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b j) * (MvPowerSeries.X j : MvPowerSeries ι C))) ∧ ∀ (κ : J) (μ : ι →₀ ℕ), MvPowerSeries.coeff μ (linPull e (S.ze t κ)) = -∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.be c s κ * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) := by
  first | exact @GlobalTheory.MainTerm.linPull_coords | exact GlobalTheory.MainTerm.linPull_coords | (intros; apply GlobalTheory.MainTerm.linPull_coords <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.limitIdempotent_range_le_sum_eigenspaces : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∀ E : Matrix κ κ C, (∀ (N : ℕ) (v : κ → C) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (E.mulVec v i - (L (ε ^ (V.l ^ n))).mulVec v i)) → ∀ v : κ → C, ∃ w : ZMod d → κ → C, (∀ a x, (L x).mulVec (w a) = em a x • w a) ∧ E.mulVec v = ∑ a, w a := by
  first | exact @GlobalTheory.IdemRange.limit_idempotent_range | exact GlobalTheory.IdemRange.limit_idempotent_range | (intros; apply GlobalTheory.IdemRange.limit_idempotent_range <;> assumption)
end
