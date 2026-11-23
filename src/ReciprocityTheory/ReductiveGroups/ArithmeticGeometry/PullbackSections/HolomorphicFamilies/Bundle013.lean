module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem coprime_two_sq {R : Type*} [CommRing R] (I J : Ideal R) (M : ℕ) (hM : Odd M) (hI : (M : R) ∈ I)
    (hIJ : I ⊔ J = ⊤) : IsCoprime (Ideal.span {(2 : R)} * J ^ 2) I := by
  have h2 : IsCoprime (Ideal.span {(2 : R)}) I := by
    rw [Ideal.isCoprime_iff_exists]
    obtain ⟨k, hk⟩ := hM
    refine ⟨-(2 * (k : R)), ?_, (M : R), hI, ?_⟩
    · exact (Ideal.span {(2 : R)}).neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self 2))
    · rw [hk]; push_cast; ring
  have hJ : IsCoprime J I := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hIJ
  exact IsCoprime.mul_left h2 hJ.pow_left

theorem exists_rep {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] (A B : Ideal R) (h : IsCoprime A B)
    (x : N) : ∃ x2 : N, x2 ∈ A • (⊤ : Submodule R N) ∧ x2 - x ∈ B • (⊤ : Submodule R N) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  refine ⟨a • x, Submodule.smul_mem_smul ha Submodule.mem_top, ?_⟩
  have hx : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
  have e : a • x - x = -(b • x) := by
    calc a • x - x = a • x - (a • x + b • x) := by rw [hx]
      _ = -(b • x) := by abel
  rw [e]
  exact Submodule.neg_mem _ (Submodule.smul_mem_smul hb Submodule.mem_top)

theorem M_mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
  have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h1
  exact Ideal.mul_le_left h1

theorem coprime_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    IsCoprime (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) l.Mb :=
  coprime_two_sq l.Mb _ l.M l.odd (M_mem_Mb l) l.coprime

theorem rep_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (l : Level H)
    (x : Dw.La) :
    ∃ x2 : Dw.La,
      x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La) ∧
      x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
  exists_rep _ _ (coprime_level l) x

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

section

set_option autoImplicit false


noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MixEnd

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section Pmaps

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem val_pmaps' (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hm : PMaps w φ' φ ε a t h) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z)
    (J₀ : (Z ⟶ X) → L.ι) (J : (Z ⟶ X') → L'.ι) (hJ₀ : Good L z J₀) (hJ : Good L' z J) :
    val t (r ≫ h) z J₀ =
      (∏ k, gw w (r ≫ φ' k) z (J₀ ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  have hp : ∀ k, (r ≫ h) ≫ φ k = (r ≫ φ' k) ≫ F := fun k => by
    rw [Category.assoc, Category.assoc, hc]
  have h1 : ∀ k, F (φ' k (r z)) ∈ L.U (J₀ ((r ≫ h) ≫ φ k)) := by
    intro k
    convert hJ₀ ((r ≫ h) ≫ φ k) using 2
    rw [hp]
    first | rfl | simp
  have h2 : ∀ k, φ' k (r z) ∈ L'.U (J (r ≫ φ' k)) := fun k => hJ (r ≫ φ' k)
  have key := hm Z r z (fun k => J₀ ((r ≫ h) ≫ φ k)) (fun k => J (r ≫ φ' k)) h1 h2
  unfold val
  refine key.trans ?_
  simp only [hp]

end Pmaps

theorem val_rigPow {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) (rig : LB.Gen (L.pull (eSec A))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    val (rigPow A L rig k) r z J = (val (L := L) (K := PUnit) (φ := fun _ => eSec A) (ε := fun _ => 1) rig r z J) ^ k := by
  unfold val
  simp only [rigPow]
  exact map_zpow _ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
  {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)

section Snd

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

theorem genSnd_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : PGen w)
    (eA : A.left ⟶ A.left) (eG : G.left ⟶ G.left) (hce : eA ≫ φ = φ ≫ eG) (ε : Fin 2 → ℤ)
    (α₀' : LB.Gen (LB.LinComb L₁ ![𝟙 A.left, eA] ε)) (α₀ : LB.Gen (LB.LinComb L₀ ![𝟙 G.left, eG] ε))
    (hPM : PMaps w ![𝟙 A.left, eA] ![𝟙 G.left, eG] ε α₀' α₀ φ)
    (mA : T ⊗ A ⟶ A) (mG : T₀ ⊗ G ⟶ G) (hmA : mA.left = (snd T A).left ≫ eA)
    (hmG : mG.left = (snd T₀ G).left ≫ eG)
    (α : LB.Gen (LB.LinComb L₀ ![(snd T₀ G).left, mG.left] ε)) (hα : α.IsGen)
    (hαc : LB.Gen.Corr L₀ _ _ _ _ α (LB.pullGen L₀ _ _ α₀ (snd T₀ G).left)) :
    ∃ α' : LB.Gen (LB.LinComb L₁ ![(snd T A).left, mA.left] ε), α'.IsGen ∧
      PMaps w ![(snd T A).left, mA.left] ![(snd T₀ G).left, mG.left] ε α' α (psiO hp τ hτ).left ∧
      LB.Gen.Corr L₁ _ _ _ _ α' (LB.pullGen L₁ _ _ α₀' (snd T A).left) := by
  have hc1 : ∀ k, (![(snd T A).left, mA.left] : Fin 2 → _) k ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, mG.left] : Fin 2 → _) k := by
    intro k; fin_cases k
    · exact (psi_snd hp τ hτ).symm
    · show mA.left ≫ φ = (psiO hp τ hτ).left ≫ mG.left
      rw [hmA, hmG, Category.assoc, hce, ← Category.assoc, ← psi_snd hp τ hτ, Category.assoc]
  have hc2 : ∀ k, (![𝟙 A.left, eA] : Fin 2 → _) k ≫ φ = φ ≫ (![𝟙 G.left, eG] : Fin 2 → _) k := by
    intro k; fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Category.id_comp, Category.comp_id]
    · exact hce
  obtain ⟨α', g', hm⟩ := exists_gen_move hL₀ hL₁ w hw _ _ ε (psiO hp τ hτ).left hc1 α hα
  refine ⟨α', g', hm, corr_of_val hL₁ fun y J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
  have hJ₀' : Good L₀ y J₀ := hJ₀
  have p1 := val_pmaps' w hc1 hm (𝟙 _) y J₀ J hJ₀' hJ
  have p2 := val_pmaps' w hc2 hPM (snd T A).left y J₀ J hJ₀' hJ
  have c := val_corr hJ₀' hαc (psiO hp τ hτ).left
  rw [val_pull hJ₀', psi_snd hp τ hτ] at c
  rw [Category.id_comp, c, p2] at p1
  simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
    Category.id_comp, hmA] at p1
  rw [val_pull hJ, Category.id_comp]
  exact (mul_left_cancel p1).symm

end Snd

end ReciprocityTheory.ChartRestriction.G.PullbackSections.MixEnd
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma dmin_ortho {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin
  rw [hx τ]
  clear hx
  unfold lminor
  rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  apply Finset.prod_eq_one
  rintro a -
  simp only [Function.comp_apply]
  generalize (↑(Fin.castLE _ a) : ℕ) = b
  clear a
  clear x τ i
  unfold sgn
  split_ifs <;> simp

lemma pnorm_unit {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hu : ∀ τ i, ‖dmin X.Gm x τ i‖ = 1) : X.pnorm la P x = ‖P x‖ := by
  unfold Data.pnorm
  simp [hu]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit
end
end
