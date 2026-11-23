module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle024
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle027
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdjointnessSeriesOfFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem neg_log_sqrt_le_of_jbound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (dg n : ℕ) (P : I2.Par X dg) (S tableLineDegreeFive cc : ℝ), (Real.pi⁻¹) ^ dg * P.Jbound n ≤ S → p14 E X.r n P.m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (P.m : ℝ) ^ 4 * (I2.dstar (E := E) P.m : ℝ) ^ 4 * I2.RR (E := E) / P.q ≤ cc → -Real.log (Real.sqrt S) ≤ tableLineDegreeFive * dg + cc * P.ph := by
  intro E _ _ _ X dg n P S tableLineDegreeFive cc hS hP14 hcc
  have hf : 0 < I2.PT.f E := by
    have h1 := P.hfr
    rcases Nat.eq_zero_or_pos (I2.PT.f E) with h | h
    · rw [h] at h1; simp at h1
    · exact h
  have hdp : 0 < I2.dstar (E := E) P.m := Nat.mul_pos (Nat.mul_pos two_pos hf) P.hm1
  have hd0 : (1 : ℝ) ≤ (I2.dstar (E := E) P.m : ℝ) := by exact_mod_cast hdp
  have hd : (0 : ℝ) < 2 * (I2.dstar (E := E) P.m : ℝ) := by linarith
  have hB := Real.rpow_pos_of_pos hd ((I2.dstar (E := E) P.m : ℝ) / 2)
  have h6 : (0 : ℝ) < 6 * (2 * (I2.dstar (E := E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2) :=
    mul_pos (by norm_num) hB
  have hph : 0 ≤ P.ph := by
    unfold I2.Par.ph I2.PT.ph
    split_ifs <;> positivity
  have hA : (4 : ℝ)⁻¹ ^ n ≠ 0 := by positivity
  have hBn : (6 * (2 * (I2.dstar (E := E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2))⁻¹ ^ n ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero h6.ne')
  have hC : (2 : ℝ)⁻¹ ^ ((X.r + 2) * dg) ≠ 0 := by positivity
  have hJpos : 0 < P.Jbound n := by
    unfold I2.Par.Jbound
    exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (inv_pos.2 h6) _))
      (pow_pos (by norm_num) _)) (Real.exp_pos _)
  have hJ : Real.log (P.Jbound n) = -(n * Real.log 4) -
      n * (Real.log 6 + (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ))) -
      (((X.r + 2) * dg : ℕ) : ℝ) * Real.log 2 -
      2 * (8100 * Real.pi * n * (P.m : ℝ) ^ 4 * (I2.dstar (E := E) P.m : ℝ) ^ 4 * I2.RR (E := E) / P.q * P.ph) := by
    unfold I2.Par.Jbound
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero hA hBn) hC) (Real.exp_pos _).ne',
      Real.log_mul (mul_ne_zero hA hBn) hC, Real.log_mul hA hBn, Real.log_exp, Real.log_pow,
      Real.log_pow, Real.log_pow, Real.log_inv, Real.log_inv, Real.log_inv,
      Real.log_mul (by norm_num) hB.ne', Real.log_rpow hd]
    unfold I2.Cchi
    ring
  have hdg : (1 : ℝ) ≤ dg := by exact_mod_cast P.hDF
  have h24 : Real.log 24 = Real.log 4 + Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hl2d : 0 ≤ Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := Real.log_nonneg (by linarith)
  have hT : 0 ≤ Real.log 24 + (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by
    have : 0 < Real.log 24 := Real.log_pos (by norm_num)
    have : 0 ≤ (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by positivity
    linarith
  have hpi : (0 : ℝ) < (Real.pi⁻¹) ^ dg := pow_pos (inv_pos.2 Real.pi_pos) _
  have hpos : 0 < (Real.pi⁻¹) ^ dg * P.Jbound n := mul_pos hpi hJpos
  have hlS := Real.log_le_log hpos hS
  rw [Real.log_mul hpi.ne' hJpos.ne', Real.log_pow, Real.log_inv, hJ] at hlS
  rw [Real.log_sqrt (hpos.le.trans hS)]
  have e2 := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hT) (sub_nonneg.2 hdg)
  have e3 := mul_le_mul_of_nonneg_right hcc hph
  have e4 := mul_le_mul_of_nonneg_right hP14 (by linarith : (0 : ℝ) ≤ dg)
  unfold p14 at e4
  push_cast at hlS
  rw [h24] at e2 e4
  linarith [e2, e3, e4]

end GlobalTheory.AnVal
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mem_iff_modN (k : ℕ) (x : Dw.La) :
    x ∈ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) ↔ Dw.ModN k x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨b, _, hb⟩ => ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩,
    fun ⟨b, hb⟩ => ⟨b, trivial, by rw [hb, Nat.cast_smul_eq_nsmul]⟩⟩

theorem mk_eq_iff (k : ℕ) (a b : Dw.La) :
    (Submodule.Quotient.mk a : LatMod Dw k) = Submodule.Quotient.mk b ↔ Dw.ModN k (a - b) := by
  rw [Submodule.Quotient.eq, mem_iff_modN]

theorem finite_latMod (k : ℕ) (hk : 0 < k) : Finite (LatMod Dw k) := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient Dw k hk
  refine Finite.of_surjective (fun j => (Submodule.Quotient.mk (r j) : LatMod Dw k)) fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨π a, (mk_eq_iff k _ _).2 ((hπ _ _).1 (hr _))⟩

theorem nsmul_latMod (k : ℕ) (q : LatMod Dw k) : k • q = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_iff_modN]
  exact ⟨a, Nat.cast_smul_eq_nsmul _ _ _⟩

variable (Xo : Moduli Dw l)

theorem exists_descend (k : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (ev : Dw.La → (ptO Xo x0 ⟶ Xo.univ.t.G)) (hadd : ∀ a b, ev (a + b) = ev a * ev b)
    (hlin : ∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) (hker : ∀ a, ev (k • a) = 1)
    (hinj : ∀ (K : Type) [Field K] (χ : S →+* K) (a b : Dw.La),
      spMap χ ≫ (ev a).left = spMap χ ≫ (ev b).left → Dw.ModN k (a - b)) :
    ∃ ev' : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G), IsFullLev Xo k x0 ev' ∧
      ∀ a, ev' (Submodule.Quotient.mk a) = ev a := by
  choose r hr using Submodule.Quotient.mk_surjective (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La)
  have h : ∀ a, ev (r (Submodule.Quotient.mk a)) = ev a := fun a => by
    obtain ⟨b, hb⟩ := (mk_eq_iff k _ _).1 (hr (Submodule.Quotient.mk a))
    rw [sub_eq_iff_eq_add.1 hb, hadd, hker, _root_.one_mul]
  refine ⟨fun q => ev (r q), ⟨fun a b => ?_, fun o a => ?_, fun K _ χ a b hab => ?_⟩, h⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    beta_reduce
    rw [← Submodule.Quotient.mk_add, h, h, h, hadd]
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    beta_reduce
    rw [← Submodule.Quotient.mk_smul, h, h, hlin]
  · rw [← hr a, ← hr b]
    exact (mk_eq_iff k _ _).2 (hinj K χ _ _ hab)

theorem pow_eq_one {k : ℕ} {S : Type} [CommRing S] {x0 : Sp S ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (h : IsFullLev Xo k x0 ev) (q : LatMod Dw k) : ev q ^ k = 1 := by
  let f : LatMod Dw k →+ Additive (ptO Xo x0 ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun q => Additive.ofMul (ev q)) fun a b => congrArg Additive.ofMul (h.1 a b)
  have := map_nsmul f k q
  rw [nsmul_latMod, map_zero] at this
  exact (congrArg Additive.toMul this).symm

theorem baseChange {k : ℕ} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x0 : Sp S ⟶ Xo.X}
    {x1 : Sp T ⟶ Xo.X} (h : ptO Xo x1 ⟶ ptO Xo x0) (hh : h.left = spMap ψ)
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) :
    IsFullLev Xo k x1 (fun q => h ≫ ev q) := by
  refine ⟨fun a b => ?_, fun o a => ?_, fun K _ χ a b hab => hev.2.2 K (χ.comp ψ) a b ?_⟩
  · beta_reduce
    rw [hev.1, MonObj.comp_mul]
  · beta_reduce
    rw [hev.2.1, Category.assoc]
  · have : spMap χ ≫ h.left ≫ (ev a).left = spMap χ ≫ h.left ≫ (ev b).left := hab
    rw [hh] at this
    rw [spMap_comp, Category.assoc, Category.assoc]
    exact this

theorem eq_of_agree (hL : Laws) {k : ℕ} (hk : 0 < k) {S T : Type} [CommRing S] [CommRing T] (χ : S →+* T)
    (hχ : ∀ e, χ e = 1 → IsUnit e) {x0 : Sp S ⟶ Xo.X} {a b : ptO Xo x0 ⟶ Xo.univ.t.G} (ha : a ^ k = 1)
    (hb : b ^ k = 1) (hab : spMap χ ≫ a.left = spMap χ ≫ b.left) : a = b := by
  obtain ⟨e, he, He⟩ := exists_isIdempotentElem_torsion_eq hL E H Dw l Xo S x0 k hk a b ha hb
  have h1 : e = 1 := (hχ e ((He T χ).2 hab)).mul_left_cancel (he.eq.trans (_root_.mul_one _).symm)
  have h2 := (He S (RingHom.id S)).1 h1
  have h3 : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id (CommRingCat.of S)
  rw [h3] at h2
  exact Over.OverMorphism.ext ((Category.id_comp _).symm.trans (h2.trans (Category.id_comp _)))

theorem exists_geometric (hL : Laws) {k : ℕ} (hk : 0 < k) (K : Type) [Field K] [IsAlgClosed K] (x0 : Sp K ⟶ Xo.X) :
    ∃ ev, IsFullLev Xo k x0 ev ∧ ∀ p : ptO Xo x0 ⟶ Xo.univ.t.G, p ^ k = 1 → ∃ q, ev q = p := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x0 ≫ Xo.s)
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x0 β.hom hβ.symm
  obtain ⟨ev, hev, h⟩ := exists_descend Xo k x0 (I.ev k) (I.add k) (I.lin k) (fun a => (I.ker k hk _).2 ⟨a, rfl⟩)
    fun K' _ χ a b hab => by
      have h1 : I.ev k a = I.ev k b :=
        eq_of_agree Xo hL hk χ (fun e he => isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at he)
          ((I.onto k hk _).2 ⟨_, rfl⟩) ((I.onto k hk _).2 ⟨_, rfl⟩) hab
      have h2 : I.ev k a = I.ev k (a - b) * I.ev k b := by rw [← I.add, sub_add_cancel]
      rw [h2, mul_eq_right, I.ker k hk] at h1
      exact h1
  refine ⟨ev, hev, fun p hp => ?_⟩
  obtain ⟨a, ha⟩ := (I.onto k hk p).1 hp
  exact ⟨_, (h a).trans ha⟩

theorem onto_of_local (hL : Laws) {k : ℕ} (hk : 0 < k) {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) (p : ptO Xo x0 ⟶ Xo.univ.t.G)
    (hp : p ^ k = 1) : ∃ q, ev q = p := by
  haveI := finite_latMod (Dw := Dw) k hk
  let K := AlgebraicClosure (IsLocalRing.ResidueField T)
  let χ : T →+* K := (algebraMap (IsLocalRing.ResidueField T) K).comp (IsLocalRing.residue T)
  have hχ : ∀ e, χ e = 1 → IsUnit e := fun e he => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    simp [χ, h0] at he
  let h : ptO Xo (spMap χ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap χ) rfl
  obtain ⟨ev₀, -, h₀⟩ := exists_geometric Xo hL hk K (spMap χ ≫ x0)
  have hpow : ∀ a : ptO Xo x0 ⟶ Xo.univ.t.G, a ^ k = 1 → (h ≫ a) ^ k = 1 := fun a ha => by
    rw [← MonObj.comp_pow, ha, MonObj.comp_one]
  choose f hf using fun q => h₀ (h ≫ ev q) (hpow _ (pow_eq_one Xo hev q))
  have hinj : Function.Injective f := fun a b hab => hev.2.2 K χ a b
    (congrArg CommaMorphism.left ((hf a).symm.trans ((congrArg ev₀ hab).trans (hf b))))
  obtain ⟨r, hr⟩ := h₀ (h ≫ p) (hpow p hp)
  obtain ⟨q, rfl⟩ := Finite.surjective_of_injective hinj r
  exact ⟨q, eq_of_agree Xo hL hk χ hχ (pow_eq_one Xo hev q) hp
    (congrArg CommaMorphism.left ((hf q).symm.trans hr))⟩

theorem injective_of_local {k : ℕ} {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) : Function.Injective ev :=
  fun a b hab => hev.2.2 _ (IsLocalRing.residue T) a b (by rw [hab])

theorem exists_levGrp (hL : Laws) {k : ℕ} (hk : 0 < k) {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev ev' : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) (hev' : IsFullLev Xo k x0 ev') :
    ∃ g : LevGrp Dw k, ∀ q, ev' q = ev (g q) := by
  haveI := finite_latMod (Dw := Dw) k hk
  choose f hf using fun q => onto_of_local Xo hL hk hev (ev' q) (pow_eq_one Xo hev' q)
  have hi := injective_of_local Xo hev
  let g : LatMod Dw k →ₗ[𝓞 E] LatMod Dw k :=
    { toFun := f
      map_add' := fun a b => hi (by rw [hev.1, hf, hf, hf, hev'.1])
      map_smul' := fun o a => hi (by rw [RingHom.id_apply, hev.2.1, hf, hf, hev'.2.1]) }
  have hg : Function.Injective g := fun a b hab => injective_of_local Xo hev'
    ((hf a).symm.trans ((congrArg ev hab).trans (hf b)))
  exact ⟨LinearEquiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩, fun q => (hf q).symm⟩

end FullLevel


open FullLevel in
theorem fullLevel_cover_baseChange_torsor :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (k : ℕ), 0 < k → (∀ (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X), ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (ev : LatMod Dw k → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ IsFullLev Xo k (spMap φ ≫ x0) ev) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ ev, IsFullLev Xo k x0 ev → IsFullLev Xo k x1 (fun q => h ≫ ev q) ∧ ∀ q, ev q ^ k = 1) ∧ (∀ (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)), IsFullLev Xo k x0 ev → (∀ p : ptO Xo x0 ⟶ Xo.univ.t.G, p ^ k = 1 → ∃ q, ev q = p) ∧ ∀ ev', IsFullLev Xo k x0 ev' → ∃ g : LevGrp Dw k, ∀ q, ev' q = ev (g q)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x0 : Sp K ⟶ Xo.X), ∃ ev, IsFullLev Xo k x0 ev := by
  intro hL E _ _ _ H Dw l Xo k hk
  refine ⟨fun S _ x0 => ?_, fun S T _ _ ψ x0 x1 h hh ev hev => ⟨FullLevel.baseChange Xo ψ h hh hev, FullLevel.pow_eq_one Xo hev⟩,
    fun T _ _ x0 ev hev => ⟨FullLevel.onto_of_local Xo hL hk hev, fun ev' hev' => FullLevel.exists_levGrp Xo hL hk hev hev'⟩,
    fun K _ _ x0 => (FullLevel.exists_geometric Xo hL hk K x0).imp fun _ h => h.1⟩
  obtain ⟨B, _, φ, ev, hφ, h1, h2, h3, h4⟩ := exists_faithfullyFlat_linear_level hL E H Dw l Xo S x0 k hk
  obtain ⟨ev', hev', -⟩ := FullLevel.exists_descend Xo k (spMap φ ≫ x0) ev h1 h2 h3 h4
  exact ⟨B, inferInstance, φ, ev', hφ, hev'⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

open scoped ContDiff

theorem filter_col_toMultiset {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
    (m : Formalism.L2.Pj.Letter T r n →₀ ℕ) (b : Fin n) :
    (Finsupp.toMultiset m).filter (fun ℓ => ℓ.2.2 = b) =
      (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm
        fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩)).map
        (fun ℓ : (Σ τ : T, Fin (r τ)) => (⟨ℓ.1, ℓ.2, b⟩ : Formalism.L2.Pj.Letter T r n)) := by
  classical
  have hinj : Function.Injective
      (fun ℓ : (Σ τ : T, Fin (r τ)) => (⟨ℓ.1, ℓ.2, b⟩ : Formalism.L2.Pj.Letter T r n)) := by
    intro x y h
    exact congrArg (fun ℓ : Formalism.L2.Pj.Letter T r n => (⟨ℓ.1, ℓ.2.1⟩ : Σ τ : T, Fin (r τ))) h
  ext ⟨τ, i, c⟩
  rw [Multiset.count_filter]
  by_cases h : c = b
  · subst h
    rw [if_pos rfl]
    have := Multiset.count_map_eq_count' _ (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm
        fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, c⟩)) hinj ⟨τ, i⟩
    rw [this]
    simp [Finsupp.count_toMultiset]
  · rw [if_neg h]
    symm
    rw [Multiset.count_eq_zero, Multiset.mem_map]
    rintro ⟨x, -, hx⟩
    exact h (congrArg (fun ℓ : Formalism.L2.Pj.Letter T r n => ℓ.2.2) hx).symm

theorem polyDeriv_prod_cols : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (T : Type) [Fintype T] (r : T → ℕ) (n : ℕ) (u : (Σ τ : T, Fin (r τ)) → V) (θ : Fin n → V → ℂ), (∀ b, Differentiable ℂ (θ b)) → ∀ P : MvPolynomial (Formalism.L2.Pj.Letter T r n) ℂ, I2.polyDeriv P (fun ℓ => (Pi.single ℓ.2.2 (u ⟨ℓ.1, ℓ.2.1⟩) : Fin n → V)) (fun z => ∏ b, θ b (z b)) 0 = ∑ m ∈ P.support, P.coeff m * ∏ b, I2.polyDeriv (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩) (1 : ℂ)) u (θ b) 0 := by
  intro V _ _ _ T _ r n u θ hθ P
  classical
  have hω : ∀ b x, ContDiffAt ℂ ω (θ b) x := fun b x =>
    GlobalTheory.SCV.contDiffAt_of_differentiableOn (hθ b).differentiableOn Filter.univ_mem ω
  have hs : ∀ b, ContDiff ℂ (⊤ : ℕ∞) (θ b) := fun b =>
    contDiff_iff_contDiffAt.2 fun x => (hω b x).of_le le_top
  rw [I2.polyDeriv_eq_of_subset P _ _ _ (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [I2.pdTerm_eq_itD]
  have e : (Finsupp.toMultiset m).toList.map
      (fun ℓ : Formalism.L2.Pj.Letter T r n => (Pi.single ℓ.2.2 (u ⟨ℓ.1, ℓ.2.1⟩) : Fin n → V)) =
      ((Finsupp.toMultiset m).toList.map
        (fun ℓ : Formalism.L2.Pj.Letter T r n => ((ℓ.2.2, u ⟨ℓ.1, ℓ.2.1⟩) : Fin n × V))).map
        (fun p => Pi.single p.1 p.2) := by
    rw [List.map_map]; rfl
  rw [e, I2.itD_prod hs]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD]
  refine lD_perm (hω b 0) ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe u, Multiset.coe_toList]
  have h := congrArg (Multiset.map fun ℓ : Formalism.L2.Pj.Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩)
    (filter_col_toMultiset m b)
  rw [Multiset.map_map] at h
  refine Eq.trans ?_ h
  conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset m)]
  rw [Multiset.filter_coe, Multiset.map_coe]
  unfold I2.colL
  rw [List.filter_map, List.map_map]
  rfl

end GlobalTheory.AnVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_faithfullyFlat_full_linear_level_structure : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (k : ℕ), 0 < k → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (ev : Dw.La → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev (k • a) = 1) ∧ ∀ (K : Type) [Field K] (χ : B →+* K) (a b : Dw.La), spMap χ ≫ (ev a).left = spMap χ ≫ (ev b).left → Dw.ModN k (a - b) := by
  first | exact @GlobalTheory.exists_faithfullyFlat_linear_level | exact GlobalTheory.exists_faithfullyFlat_linear_level | (intros; apply GlobalTheory.exists_faithfullyFlat_linear_level <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.framedPoint_generator_ringBaseChange : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] (ψ : S →+* T) (y : FrPt Xo c S) (h : ptO Xo (spMap ψ ≫ y.x) ⟶ ptO Xo y.x), h.left = spMap ψ → ∀ s' : LB.Sec (PPx (spMap ψ ≫ y.x)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s s' → ∀ s'' : LB.Sec (PPx (spMap ψ ≫ y.x)), ∃! a : T, ∀ i, s''.f i = scal (spMap ψ ≫ y.x) a i * s'.f i := by
  first | exact @GlobalTheory.framedPoint_generator_baseChange | exact GlobalTheory.framedPoint_generator_baseChange | (intros; apply GlobalTheory.framedPoint_generator_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isotropic_enumeration_surjective_local_ring : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x0 z → (∀ a, InZh Xo Λ N a → ∃ i, z i = a) ∧ ∀ z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z' i)) → GeoInj Xo x0 z' → ∃ σ : Equiv.Perm (Fin (Λ.zCard N (Dw.p + Dw.q))), ∀ i, z' i = z (σ i) := by
  first | exact @GlobalTheory.isotropic_enumeration_onto_of_isLocalRing | exact GlobalTheory.isotropic_enumeration_onto_of_isLocalRing | (intros; apply GlobalTheory.isotropic_enumeration_onto_of_isLocalRing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.frame_rigidification_of_canonical_axes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∀ wP : PrimTyG t, IsPrimG t wP → Rig0G t x0 d x act e wP := by
  first | exact @GlobalTheory.ThetaVal.rig_of_frAxes | exact GlobalTheory.ThetaVal.rig_of_frAxes | (intros; apply GlobalTheory.ThetaVal.rig_of_frAxes <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.exists_firstPartialLaw_series_of_frames_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ ph1 : PS S 3 d, ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))) := by
  first | exact @GlobalTheory.exists_firstPartialLaw_series_of_frames | exact GlobalTheory.exists_firstPartialLaw_series_of_frames | (intros; apply GlobalTheory.exists_firstPartialLaw_series_of_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rawChart_baseChange_rig_germ_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) → ∀ (wP : PrimTy H Xo), wP.IsGen → (LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL x0 d x act e wP 0) (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt x0 S) 1) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP 0) (homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) 0 →ₐ[S'] S')).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt (spMap ψ ≫ x0) S') 1)) ∧ ∀ (k : ℕ) (Fs : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo x0))) (Fs' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo (spMap ψ ≫ x0)))) (f : MvPowerSeries (Fin 1 × Fin d) S), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (ptBC ψ x0 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) Fs Fs' → RIsGerm x0 d x act e wP k Fs f → RIsGerm (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP k Fs' (MvPowerSeries.map ψ f) := by
  first | exact @GlobalTheory.rawChart_baseChange_rig_germ | exact GlobalTheory.rawChart_baseChange_rig_germ | (intros; apply GlobalTheory.rawChart_baseChange_rig_germ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.exists_adjointness_series_of_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ ad : 𝓞 E → PS S 2 d, (∀ a, MvPowerSeries.constantCoeff (ad a) = 1) ∧ ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])) := by
  first | exact @GlobalTheory.FrameAdjSeries.exists_ad | exact GlobalTheory.FrameAdjSeries.exists_ad | (intros; apply GlobalTheory.FrameAdjSeries.exists_ad <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem isHolFam_pullback_lift : ∀ (X Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (N : ℕ) (e₁ : (Fin N → ℂ) → (Sp ℂ ⟶ Y₁)) (e₂ : (Fin N → ℂ) → (Sp ℂ ⟶ Y₂)) (u : Sp ℂ ⟶ X) (h₁ : ∀ z, e₁ z ≫ p₁ = u) (h₂ : ∀ z, e₂ z ≫ p₂ = u), IsHolFam e₁ → IsHolFam e₂ → IsHolFam (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm)) := by
  intro X Y₁ Y₂ p₁ p₂ N e₁ e₂ u h₁ h₂ hol₁ hol₂
  have ea : (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.fst p₁ p₂) = e₁ :=
    funext fun z => pullback.lift_fst _ _ _
  have eb : (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.snd p₁ p₂) = e₂ :=
    funext fun z => pullback.lift_snd _ _ _
  have ha : IsHolTo (Set.univ : Set (Fin N → ℂ))
      (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.fst p₁ p₂) := by
    rw [ea]
    intro U f
    simpa using hol₁ U f
  have hb : IsHolTo (Set.univ : Set (Fin N → ℂ))
      (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.snd p₁ p₂) := by
    rw [eb]
    intro U f
    simpa using hol₂ U f
  have hc := GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback p₁ p₂) ha hb
  intro U f
  simpa using hc U f

end GlobalTheory.AnVal
end
