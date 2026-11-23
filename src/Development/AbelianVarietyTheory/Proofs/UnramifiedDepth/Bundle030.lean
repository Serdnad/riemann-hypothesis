module

public import Development.AbelianVarietyTheory.Statements.ChartPoints.ChartPt
public import Formalism.LocalToGlobal.CharacterGerms.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle010
public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle025
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle024
import Formalism.LocalToGlobal.CharacterGerms.Bundle006
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle026
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import ReciprocityTheory.DualLattices.Bundle026
public import ReciprocityTheory.DualLattices.Bundle021
public import ReciprocityTheory.DualLattices.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvCotOfUnivDer
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvHopfOfTensorLocal
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LocalFactorModPNilOver
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle021
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniversalDerivation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Formalism.IncomingBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle009
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.TopLimitModules.LimJMemSmulTop
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

theorem linPull_coords : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (ι : Type) [Fintype ι] (e : ι → I → C) (z : I → ι → C) (al : I → ℕ → I → C), (∀ j x, e j x = ∑ b, z b j * S.tan b x) → (∀ c b, al c 0 b = if c = b then 1 else 0) → (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) → (∀ c, MvPowerSeries.constantCoeff (linPull e (t c)) = 0) ∧ (∀ (b : I) (μ : ι →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) = MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b j) * (MvPowerSeries.X j : MvPowerSeries ι C))) ∧ ∀ (κ : J) (μ : ι →₀ ℕ), MvPowerSeries.coeff μ (linPull e (S.ze t κ)) = -∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.be c s κ * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) := by
  intro C _ V d I J _ _ G S t ht ι _ e z al he hal0 hal
  obtain ⟨f, hf⟩ : ∃ f : I → MvPowerSeries ι C,
      f = fun x => ∑ j, e j x • (MvPowerSeries.X j : MvPowerSeries ι C) := ⟨_, rfl⟩
  have hlp : ∀ F : MvPowerSeries I C, linPull e F = MvPowerSeries.subst f F := by
    intro F; subst hf; rfl
  have hf0 : ∀ x, MvPowerSeries.constantCoeff (f x) = 0 := by
    intro x

    simp [hf, map_sum, MvPowerSeries.smul_eq_C_mul]
  have hsub : MvPowerSeries.HasSubst f := MvPowerSeries.hasSubst_of_constantCoeff_zero hf0
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hal' : ∀ c s x, S.al c s x = ∑ b', al c s b' * S.tan b' x := by
    intro c s x
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp only [hal0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact S.cur_zero_inl c x
    · rw [hal c s x hs]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [show S.al b' 0 x = S.tan b' x from S.cur_zero_inl b' x]
  simp only [hlp]
  refine ⟨fun c => MvPowerSeries.constantCoeff_subst_eq_zero hsub hf0 (ht.1 c), fun b μ => ?_,
    fun κ μ => ?_⟩
  · set P : I → ℕ → C := fun c s =>
      MvPowerSeries.coeff μ (MvPowerSeries.subst f (t c) ^ V.l ^ s) with hP
    set Y : I → C := fun b' => ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b' * P c s with hY
    set Zf : I → C := fun b' =>
      MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b' j) *
        (MvPowerSeries.X j : MvPowerSeries ι C)) with hZ
    have hx : ∀ x, ∑ b', (Y b' - Zf b') * S.tan b' x = 0 := by
      intro x
      have h := GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries C I ι I V.l hl (fun c s => S.al c s x) t (MvPowerSeries.X x) f hf0 ht.1
        (fun μ' => by rw [MvPowerSeries.coeff_X, ht.2 x μ']) μ
      rw [MvPowerSeries.subst_X hsub] at h
      have eL : MvPowerSeries.coeff μ (f x) = ∑ b', Zf b' * S.tan b' x := by

        simp only [hf, hZ, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_C_mul, he,
        Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have eR : ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.al c s x *
          MvPowerSeries.coeff μ (MvPowerSeries.subst f (t c) ^ V.l ^ s) =
          ∑ b', Y b' * S.tan b' x := by
        calc _ = ∑ s ∈ Finset.range (μ.degree + 1), ∑ b', ∑ c,
              al c s b' * P c s * S.tan b' x := by
              refine Finset.sum_congr rfl fun s _ => ?_
              simp only [hP, hal', Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c _ => ?_
              ring
          _ = ∑ b', ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b' * P c s * S.tan b' x :=
              Finset.sum_comm
          _ = _ := by simp only [hY, Finset.sum_mul]
      rw [eL, eR] at h
      simp only [sub_mul, Finset.sum_sub_distrib, h, sub_self]
    have hv : Matrix.vecMul (fun b' => Y b' - Zf b') (Matrix.of S.tan) = 0 := by
      funext x
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      exact hx x
    have h0 := congrFun (Matrix.eq_zero_of_vecMul_eq_zero S.U_det_ne hv) b
    exact sub_eq_zero.mp h0
  · have hF : ∀ μ' : I →₀ ℕ, MvPowerSeries.coeff μ' (S.ze t κ) =
        ∑ s ∈ Finset.range (μ'.degree + 1), ∑ c, (-S.be c s κ) *
          MvPowerSeries.coeff μ' (t c ^ V.l ^ s) := by
      intro μ'
      show -(∑ s ∈ Finset.Icc 1 μ'.degree, ∑ c : I,
        S.be c s κ * MvPowerSeries.coeff μ' (t c ^ V.l ^ s)) = _
      simp only [neg_mul, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_subset
      · intro s hs
        simp only [Finset.mem_Icc, Finset.mem_range] at hs ⊢
        omega
      · intro s hs hns
        have hs0 : s = 0 := by
          simp only [Finset.mem_Icc, Finset.mem_range] at hs hns
          omega
        subst hs0
        simp [show ∀ c, S.be c 0 κ = 0 from fun c => S.be_zero c κ]
    rw [GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries C I ι I V.l hl (fun c s => -S.be c s κ) t (S.ze t κ) f hf0 ht.1 hF μ]
    simp only [neg_mul, Finset.sum_neg_distrib]

end GlobalTheory.MainTerm
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.chainStep_kernel_rank_le_mod_maxIdeal : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s + 1 < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → ∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν e, D.lev e = s + 1 → V.MM (∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2))) → N ≤ X.j' := by
  first | exact @GlobalTheory.ChainStep.rank_le | exact GlobalTheory.ChainStep.rank_le | (intros; apply GlobalTheory.ChainStep.rank_le <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.independentMod_firstCoeff_chainLastStep : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → IndepMod V (fun δ (κ : J g) => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), y δ c ^ V.l * ((V.l : C) * S.be c 1 κ)) := by
  first | exact @GlobalTheory.LastStep.indepMod_first_coeff | exact GlobalTheory.LastStep.indepMod_first_coeff | (intros; apply GlobalTheory.LastStep.indepMod_first_coeff <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChTor

namespace GlobalTheory.ChTor

theorem exists_genericPoint_hom (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C)) (G : Over (Sp O)) [GrpObj G] (hsep : IsSeparated G.hom)
    (A : Over (Sp C)) [GrpObj A] (gen : A.left ⟶ G.left)
    (h : IsGrpPullback A G (spMap (algebraMap O C)) gen) :
    ∃ j : (algOver O O ⟶ G) →* Pts A, Function.Injective j ∧
      ∀ P z, z.left ≫ gen = spMap (algebraMap O C) ≫ P.left ↔ z = j P := by
  have hid : spMap (algebraMap O O) = 𝟙 (Sp O) := by
    simp [spMap]
  let e₀ : (Over.mk ((Over.mk (𝟙 (Sp C)) : Over (Sp C)).hom ≫ spMap (algebraMap O C)) : Over (Sp O)) ⟶ algOver O O :=
    Over.homMk (spMap (algebraMap O C)) (by
      change spMap (algebraMap O C) ≫ spMap (algebraMap O O) = 𝟙 _ ≫ spMap (algebraMap O C)
      rw [hid, Category.comp_id, Category.id_comp])
  have hw : ∀ P : algOver O O ⟶ G,
      (spMap (algebraMap O C) ≫ P.left) ≫ G.hom = 𝟙 (Sp C) ≫ spMap (algebraMap O C) := fun P => by
    have := Over.w (e₀ ≫ P)
    exact this
  let j₀ : (algOver O O ⟶ G) → Pts A := fun P =>
    Over.homMk (h.1.lift (spMap (algebraMap O C) ≫ P.left) (𝟙 (Sp C)) (hw P)) (h.1.lift_snd _ _ _)
  have hj : ∀ P, (j₀ P).left ≫ gen = spMap (algebraMap O C) ≫ P.left := fun P => h.1.lift_fst _ _ _
  have key : ∀ (P : algOver O O ⟶ G) (z : Pts A),
      z.left ≫ gen = spMap (algebraMap O C) ≫ P.left ↔ z = j₀ P := fun P z => by
    constructor
    · intro hz
      refine Over.OverMorphism.ext (h.1.hom_ext (hz.trans (hj P).symm) ?_)
      exact (Over.w z).trans (Over.w (j₀ P)).symm
    · rintro rfl
      exact hj P
  have hmul : ∀ P Q, j₀ (P * Q) = j₀ P * j₀ Q := fun P Q => by
    refine ((key _ _).1 ?_).symm
    have e := h.2 _ (j₀ P) (j₀ Q) (e₀ ≫ P) (e₀ ≫ Q) (hj P).symm (hj Q).symm
    rw [← MonObj.comp_mul] at e
    exact e.symm
  refine ⟨MonoidHom.mk' j₀ hmul, fun P Q hPQ => ?_, key⟩
  have hPQ' : j₀ P = j₀ Q := hPQ
  haveI : IsDomain O := hinj.isDomain _
  haveI : IsDominant (spMap (algebraMap O C)) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap O C)).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  refine Over.OverMorphism.ext ?_
  refine ext_of_isDominant_of_isSeparated (X := Sp O) G.hom ?_ (spMap (algebraMap O C)) ?_
  · exact (Over.w P).trans (Over.w Q).symm
  · exact (hj P).symm.trans (by rw [hPQ']; exact hj Q)

end GlobalTheory.ChTor
end
end

section

noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.GaugeCocycle

open MvPowerSeries

variable {C : Type} [Field C]

def valRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

theorem intS_iff_ig (V : VF C) {σ : Type} (f : MvPowerSeries σ C) : IntS V f ↔ f ∈ Ig (valRing V) C σ := by
  constructor
  · intro hf
    let g : MvPowerSeries σ (valRing V) := fun n => ⟨coeff n f, hf n⟩
    refine RingHom.mem_range.2 ⟨g, ?_⟩
    ext n
    rw [coeff_map]
    rfl
  · intro hf n
    obtain ⟨g, rfl⟩ := RingHom.mem_range.1 hf
    rw [coeff_map]
    exact (coeff n g).2

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {d : ℕ}

omit [CharZero C] in
theorem map_self {σ : Type} (f : MvPowerSeries σ C) : MvPowerSeries.map (algebraMap C C) f = f := by
  ext n
  rw [coeff_map]
  rfl

end GlobalTheory.GaugeCocycle
end
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_saturated_good_vectors_small_corank : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] (G : Cart V d I J) (a : ZMod d), ∃ (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C), (∀ ν, G.Good a (w ν) (x ν)) ∧ (∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0) ∧ IsSat V w ∧ (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a).card ≤ N + (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1).card := by
  first | exact @GlobalTheory.GoodCorank.exists_good_sat | exact GlobalTheory.GoodCorank.exists_good_sat | (intros; apply GlobalTheory.GoodCorank.exists_good_sat <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.hPullW_upG_twoGroupEmbedding_eq_rename : ∀ (C : Type) [Field C] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (g : Fin 2) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ F : MvPowerSeries (I g) C, hPullW (upG g F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inl (linPull e F)) ∧ ∀ F : MvPowerSeries (I (1 - g)) C, hPullW (upG (1 - g) F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inr (linPull v' F) := by
  first | exact @GlobalTheory.MainTerm.hPullW_upG_toW | exact GlobalTheory.MainTerm.hPullW_upG_toW | (intros; apply GlobalTheory.MainTerm.hPullW_upG_toW <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve
open ReciprocityTheory.ChartRestriction.G.Pdiv.TL

namespace GlobalTheory.JetExpansion

variable {k : Type} [CommRing k] {κ : Type} [Finite κ]

def tj (m : ℕ) : MvPowerSeries κ k →ₐ[k] JetR k κ m :=
  (MvPowerSeries.truncTotalAlgHom κ k (m + 1)).restrictScalars k

theorem tj_eq_iff (m : ℕ) (f g : MvPowerSeries κ k) :
    tj m f = tj m g ↔ ∀ x : κ →₀ ℕ, x.degree < m + 1 → MvPowerSeries.coeff x f = MvPowerSeries.coeff x g :=
  limJ_tt_eq_iff m f g

theorem tj_ext {f g : MvPowerSeries κ k} (h : ∀ m, tj m f = tj m g) : f = g := by
  ext x
  exact (tj_eq_iff x.degree f g).1 (h _) x (Nat.lt_succ_self _)

theorem tj_eq_zero_iff (m : ℕ) (f : MvPowerSeries κ k) :
    tj m f = 0 ↔ f ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ k)) ^ (m + 1) := by
  rw [← GlobalTheory.germIdeal_eq_span, GlobalTheory.mem_germIdeal_pow_iff, ← map_zero (tj (k := k) (κ := κ) m), tj_eq_iff]
  simp only [map_zero]

theorem exists_tj (p : ∀ m, JetR k κ m) (hp : ∀ m, jetTruncR k κ m (p (m + 1)) = p m) :
    ∃ f : MvPowerSeries κ k, ∀ m, tj m f = p m := by
  choose P hP using fun m => Ideal.Quotient.mk_surjective (p m)
  have hck : ∀ (u : κ →₀ ℕ) m, u.degree ≤ m → (P m).coeff u = (P u.degree).coeff u := by
    intro u m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [← ih]
      have h1 : (Ideal.Quotient.mk _ (P m) : JetR k κ m) = Ideal.Quotient.mk _ (P (m + 1)) := by
        rw [hP, ← hp m, ← hP]
        rfl
      exact ((limJ_mk_eq_iff m _ _).1 h1 u (by omega)).symm
  refine ⟨fun u => (P u.degree).coeff u, fun m => ?_⟩
  rw [← hP m]
  refine (limJ_mk_eq_iff m (MvPowerSeries.truncTotal (m + 1) _) _).2 fun u hu => ?_
  exact (MvPowerSeries.coeff_truncTotal _ hu).trans (hck u m (by omega)).symm

end GlobalTheory.JetExpansion
end
end

section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

noncomputable section

namespace GlobalTheory.EvClose

theorem pSerFrob {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀}
    (K : LAlg R₀) (ch : FormalChartAtZero B K g) : PSerFrobStatement p K ch :=
  GlobalTheory.pSerFrob_of_invariance @GlobalTheory.nEval_basic
    (GlobalTheory.nsmulF_add_sqZero_eq @GlobalTheory.nEval_basic (GlobalTheory.chart_fAdd_firstOrder @GlobalTheory.nEval_basic))
    @GlobalTheory.coeff_dvd_of_aeval_add_sq_zero p K ch

theorem wFrob {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p}
    {K : LAlg R₀} (wd : WData Tw K) (g : ℕ) : WFrobStatement wd g :=
  GlobalTheory.WFrob.wFrob wd g

section Leaves

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p}
  {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe]
  {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)}

theorem evLat (D : Dat p g B Tw Dt Oe σ cp) : EvLatStatement D :=
  GlobalTheory.evImg_isLat_subring D

theorem evHopf (D : Dat p g B Tw Dt Oe σ cp) : EvHopfStatement D :=
  _root_.GlobalTheory.EvHopf.evHopf_of_tensorLocal
    GlobalTheory.isLocalRing_tensorProduct_of_finite_of_points D

theorem evAct (D : Dat p g B Tw Dt Oe σ cp) : EvActStatement D :=
  GlobalTheory.EvAct.evImg_act_stable D

theorem evHt (D : Dat p g B Tw Dt Oe σ cp) : EvHtStatement D :=
  GlobalTheory.evHt_of_lam @GlobalTheory.localFactor_mod_p_nilOver D

theorem evBt (D : Dat p g B Tw Dt Oe σ cp) : EvBtStatement D :=
  GlobalTheory.evBt_of_tangent_of_series
    (GlobalTheory.chart_p_smul_lift_eq_bt (GlobalTheory.chart_fAdd_firstOrder @GlobalTheory.nEval_basic))
    (GlobalTheory.fAdd_nsmulF_eq_eval_poly_frob @GlobalTheory.nEval_basic @pSerFrob)
    @GlobalTheory.localFactor_mod_p_nilOver @wFrob D

theorem periodDatum_signCharacters_mem_evalImage (D : Dat p g B Tw Dt Oe σ cp) : EvenTwoEvaluationSign D :=
  GlobalTheory.signChar_mem_evImg D

theorem evCot (D : Dat p g B Tw Dt Oe σ cp) : EvCotStatement D :=
  GlobalTheory.evCot_of_univDer (GlobalTheory.CotUniv.universal_derivation @GlobalTheory.CotPoints.points_eq_tangent) D

def htdOfDat (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C] (v : Valuation C NNReal)
    [Algebra (Tw.O : Type) C] (hdom : IsDomain (Tw.O : Type))
    (hinj : Function.Injective (algebraMap (Tw.O : Type) C)) :
    HodgeTateDatum p g v (Tw.O : Type) Oe σ cp :=
  htd_of D C v hdom hinj (evLat D) (evHopf D) (evAct D) (evHt D) (evBt D) (periodDatum_signCharacters_mem_evalImage D) (evCot D)

end Leaves

end GlobalTheory.EvClose
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve

namespace GlobalTheory.StalkJet

variable {k : Type} [Field k]

theorem isLocalRing_of_aug {A : Type} [CommRing A] [Algebra k A] (aug : A →ₐ[k] k) {n : ℕ}
    (h : RingHom.ker aug ^ n = ⊥) : IsLocalRing A := by
  haveI : Nontrivial A := (aug : A →+* k).domain_nontrivial
  have nil : ∀ a : A, aug a = 0 → IsNilpotent a := fun a ha =>
    ⟨n, by rw [← Ideal.mem_bot, ← h]; exact Ideal.pow_mem_pow ha n⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : aug a = 0
  · exact Or.inr (nil a ha).isUnit_one_sub
  · left
    have h1 : IsNilpotent (a - algebraMap k A (aug a)) := nil _ (by simp)
    have h2 : IsUnit (algebraMap k A (aug a)) := (IsUnit.mk0 _ ha).map _
    have := h1.isUnit_add_right_of_commute h2 (Commute.all _ _)
    simpa using this

theorem exists_factor {B : Over (Sp k)} (b : B.left) [Algebra k (B.left.presheaf.stalk b)]
    (hb : B.left.fromSpecStalk b ≫ B.hom = spMap (algebraMap k (B.left.presheaf.stalk b)))
    {A : Type} [CommRing A] [Algebra k A] [IsLocalRing A] (y : algOver k A ⟶ B)
    (hy : y.left (closedPoint A) = b) :
    ∃ τ : B.left.presheaf.stalk b →ₐ[k] A, IsLocalHom τ ∧
      spMap (τ : B.left.presheaf.stalk b →+* A) ≫ B.left.fromSpecStalk b = y.left := by
  subst hy
  have e := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of A) y.left
  have w : y.left ≫ B.hom = spMap (algebraMap k A) := Over.w y
  have e2 : CommRingCat.ofHom (algebraMap k (B.left.presheaf.stalk (y.left (closedPoint A)))) ≫
      Scheme.stalkClosedPointTo (R := .of A) y.left = CommRingCat.ofHom (algebraMap k A) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    refine Eq.trans ?_ w
    exact (congrArg (Spec.map (Scheme.stalkClosedPointTo (R := .of A) y.left) ≫ ·) hb.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.hom) e))
  refine ⟨⟨(Scheme.stalkClosedPointTo (R := .of A) y.left).hom, fun c => ?_⟩, ?_, e⟩
  · exact congrArg (fun q => q.hom c) e2
  · exact ⟨(Scheme.isLocalHom_stalkClosedPointTo' (R := A) y.left).1⟩

end GlobalTheory.StalkJet
end
end
