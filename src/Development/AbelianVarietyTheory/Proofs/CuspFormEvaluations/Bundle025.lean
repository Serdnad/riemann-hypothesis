module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem symLift_exists_unique_of_cast (hLaw : Laws) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    (hk : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) (K : ℤ) (hK : K = (k : ℤ)) (T : Over S) (x : T ⟶ P.A)
    (hx : x ^ k = 1) :
    (∃ U : ThetaGrp P.A P.L K T, SymLift P.A P.L K k x U) ∧
      ∀ U U' : ThetaGrp P.A P.L K T, SymLift P.A P.L K k x U → SymLift P.A P.L K k x U' →
        LB.Gen.Corr P.L _ _ _ _ U.φ U'.φ := by
  subst hK
  refine ⟨exists_symLift_global hLaw S P k hk hu T x hx, ?_⟩
  intro U U' hU hU'
  exact SymLiftOdd.symLift_unique hLaw.globalFns P.isAb P.isLB hk U U' hU hU'

theorem moduli_univ_symLift_global :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (x : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → (∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U) ∧ ∀ U U' : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U' → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ U.φ U'.φ := by
  intro hLaw E _ _ _ H Dw l Xo N hN
  obtain ⟨hNoeth, -, hUnit, -, hP⟩ := moduli_univ_polAV E H Dw l Xo
  have := hNoeth
  have hN2 : Odd (N ^ 2) := hN.pow
  have hpos : 0 < N ^ 2 := pow_pos hN.pos 2
  refine hP (fun (A : Over Xo.X) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (_ : ℕ) =>
    ∀ (T : Over Xo.X) (x : T ⟶ A), x ^ (N ^ 2) = 1 →
      (∃ U : ThetaGrp A L ((N : ℤ) ^ 2) T, SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U) ∧
        ∀ U U' : ThetaGrp A L ((N : ℤ) ^ 2) T, SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U →
          SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U' → LB.Gen.Corr L _ _ _ _ U.φ U'.φ) ?_
  intro P T x hx
  exact symLift_exists_unique_of_cast hLaw Xo.X P (N ^ 2) hN2 (hUnit _ hpos) ((N : ℤ) ^ 2)
    (by push_cast; rfl) T x hx

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnivPairing

theorem weilIs_pow_eq_one (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  obtain ⟨hex, hmul, -, -⟩ := hW S P k T
  obtain ⟨c₁, hc₁, hu⟩ := hex 1 y (one_pow k) hy
  have h₂ := hmul 1 1 y c₁ c₁ hc₁ hc₁
  rw [_root_.mul_one] at h₂
  obtain rfl : c₁ = 1 := mul_eq_left.1 (hu _ h₂)
  have hpow : ∀ j : ℕ, WeilIs P.A P.L k (x ^ j) y (c ^ j) := fun j => by
    induction j with
    | zero => rw [pow_zero, pow_zero]; exact hc₁
    | succ j ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ _ ih hc
  have h := hpow k
  rw [hx] at h
  exact hu _ h

theorem isNilpotent_of_geometric {B : Type} [CommRing B] {b : B}
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ b = 0) : IsNilpotent b := by
  refine nilpotent_iff_mem_prime.2 fun J hJ => ?_
  have e := h (AlgebraicClosure (FractionRing (B ⧸ J)))
    (((algebraMap (FractionRing (B ⧸ J)) _).comp (algebraMap (B ⧸ J) (FractionRing (B ⧸ J)))).comp
      (Ideal.Quotient.mk J))
  rw [RingHom.comp_apply, RingHom.comp_apply, map_eq_zero,
    map_eq_zero_iff _ (IsFractionRing.injective (B ⧸ J) _)] at e
  exact Ideal.Quotient.eq_zero_iff_mem.1 e

theorem eq_one_of_geometric (B : Type) [CommRing B] (u : B) (k : ℕ) (hk : IsUnit (k : B)) (hu : u ^ k = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ u = 1) : u = 1 := by
  have hn : IsNilpotent ((∑ i ∈ Finset.range k, u ^ i) - k) := isNilpotent_of_geometric fun K _ _ χ => by
    simp [h K χ]
  have hs : IsUnit (∑ i ∈ Finset.range k, u ^ i) := by
    have := hn.isUnit_add_right_of_commute hk (Commute.all _ _)
    rwa [sub_add_cancel] at this
  have e := geom_sum_mul u k
  rw [hu, sub_self] at e
  exact sub_eq_zero.1 (hs.mul_right_eq_zero.1 e)

theorem weilIs_univ_pull_exists_unique : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), 0 < N → (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (x y : T ⟶ Xo.univ.t.G) (e : Γ(T.left, ⊤)ˣ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom e)) ∧ (∀ (T : Over Xo.X) (x y : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → ∃ e : Γ(T.left, ⊤)ˣ, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e ∧ e ^ (N ^ 2) = 1 ∧ ∀ e', WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e' → e' = e) ∧ ∀ (B : Type) [CommRing B] (u : B) (k : ℕ), IsUnit (k : B) → u ^ k = 1 → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ u = 1) → u = 1 := by
  intro hL E _ _ _ H Dw l Xo N _
  have := UnivPol.isLocallyNoetherian Xo
  refine ⟨fun T T' h x y e _ _ he => ?_, fun T x y hx hy => ?_, eq_one_of_geometric⟩
  · exact CommPairing.weilIs_pull hL.globalFns (UnivPol.pol Xo).isAb (UnivPol.pol Xo).isLB h he
  · rw [← Nat.cast_pow]
    obtain ⟨e, he, hu⟩ := (hL.weil Xo.X (UnivPol.pol Xo) (N ^ 2) T).1 x y hx hy
    exact ⟨e, he, weilIs_pow_eq_one hL.weil (UnivPol.pol Xo) (N ^ 2) x y hx hy e he, hu⟩

end GlobalTheory.UnivPairing
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace NormMulUniv

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

theorem rigPow_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigPow A L ρ k).IsGen := by
  refine isGen_of_gm _ fun y i j hi hj => ?_
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ (𝟙 S) y hi hj
  rw [trF, Fintype.prod_unique, zpow_one] at e
  refine (map_zpow _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (map_zpow _ _ _)).symm)
  rw [trF, Fintype.prod_unique, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem eSec_hom : eSec A ≫ A.hom = 𝟙 S := Over.w η[A]

theorem eSec_mulA (n : ℕ) : eSec A ≫ (mulA A n).left = eSec A := by
  have h : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by simp [Hom.one_def]
  have : (η[A] : 𝟙_ (Over S) ⟶ A) ≫ mulA A n = η[A] := by
    rw [MonObj.comp_pow, Category.comp_id, h, one_pow]
  exact congrArg (fun q => q.left) this

theorem exists_normalised (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (n : ℕ)
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])) (hβ : β.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      IsNormMul A L ρ n α := by
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![𝟙 A.left, (mulA A n).left]) (ε' := ![(n : ℤ) ^ 2, -1])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, eSec_mulA, Category.comp_id]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -(n : ℤ) ^ 2 + - -1 + ((n : ℤ) ^ 2 + -1) = 0 by ring, zpow_zero,
        _root_.mul_one])
    (LB.mulGen L _ _ _ _ β (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ β (eSec A)))
      (LB.mulGen L _ _ _ _ (rigPow A L ρ ((n : ℤ) ^ 2)) (LB.invGen L (fun _ : PUnit => eSec A) (fun _ => 1) ρ))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (rigPow_isGen hρ _) (DVR.invGen_isGen _ _ _ _ hρ))) _))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, eSec_hom, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

theorem normalised_unique (hL : L.IsLB) (hp : Function.Surjective A.hom.appTop.hom)
    {ρ : LB.Gen (L.pull (eSec A))} {n : ℕ}
    {α β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])}
    (hα : α.IsGen) (hβ : β.IsGen) (nα : IsNormMul A L ρ n α) (nβ : IsNormMul A L ρ n β) :
    LB.Gen.Corr L _ _ _ _ α β :=
  corr_of_val hL fun z J hJ => gen_unique hL A.hom (eSec A) eSec_hom hp hα hβ (fun w I hI => by
    have a := val_corr hI nα (𝟙 _)
    have b := val_corr hI nβ (𝟙 _)
    rw [val_pull hI, Category.id_comp] at a b
    exact a.trans b.symm) _ _ z J hJ

theorem exists_pull (hL : L.IsLB) {n : ℕ}
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])) (hβ : β.IsGen)
    (T : Over S) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      LB.Gen.Corr L _ _ _ _ α (LB.pullGen L _ _ β (snd T A).left) := by
  have e₁ : (snd T A).left ≫ (mulA A n).left = (snd T A ^ n).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ n).left]) (ε' := ![(n : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((n : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen L ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1] β (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ hβ _)
  exact ⟨α, hα, corr_of_val hL fun y J hJ => hv _ _ y J hJ⟩

end NormMulUniv

theorem moduli_univ_normMul :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), ∃ α₀ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![𝟙 Xo.univ.t.G.left, (mulA Xo.univ.t.G N).left] ![(N : ℤ) ^ 2, -1]), α₀.IsGen ∧ IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ ∧ (∀ α₁, α₁.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₁ → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α₁ α₀) ∧ ∀ T : Over Xo.X, ∃ α : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![(snd T Xo.univ.t.G).left, (snd T Xo.univ.t.G ^ N).left] ![(N : ℤ) ^ 2, -1]), α.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd T Xo.univ.t.G).left) := by
  intro hLaw E _ _ _ H Dw l Xo N
  have := UnivPol.isLocallyNoetherian Xo
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨β, hβ⟩ := hLaw.mulPull _ (UnivPol.pol Xo) N
  obtain ⟨α₀, h₀, n₀⟩ := NormMulUniv.exists_normalised hL Xo.univ.t.PP.rigGen N β hβ
  exact ⟨α₀, h₀, n₀, fun α₁ h₁ n₁ => NormMulUniv.normalised_unique hL
    (hLaw.globalFns _ _ (ObjDim.isAbelianScheme Xo.univ)).2 h₁ h₀ n₁ n₀, NormMulUniv.exists_pull hL α₀ h₀⟩

end GlobalTheory
end
end
